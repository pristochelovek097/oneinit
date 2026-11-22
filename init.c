#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <stdarg.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/utsname.h>
#include <sys/types.h>
#include <dirent.h>
#include <fcntl.h>
#include <signal.h>
#include <termios.h>
#include <time.h>
#include <sys/sysmacros.h>
#include <sys/reboot.h>
#include <sys/ioctl.h>
#include <sys/select.h>
#include <ctype.h>

volatile sig_atomic_t current_runlevel = 3; 
volatile sig_atomic_t child_died = 0;
volatile sig_atomic_t shutdown_requested = 0;

struct timespec boot_start;

/* массив пидов для консолей */
pid_t shell_pids[2] = {0, 0};
const char *tty_names[2] = {"tty1", "tty2"};

/* Нативный менеджер сервисов: S##/D## (start), K## (stop), <name>.levels */
#define MAX_SERVICES 32
struct service {
    char name[48];
    char start_path[192];
    char stop_path[192];
    int levels;      /* битовая маска: бит n = runlevel n */
    int order;
    int daemon;      /* D## — долгоживущий, не ждём завершения */
    int active;
    int last_status; /* код возврата последнего запуска, -1 = не запускался */
    pid_t pid;       /* 0 для oneshot-сервисов */
};
static struct service services[MAX_SERVICES];
static int service_count = 0;

static void setup_signals(void);
static void do_log(const char *fmt, ...);
static void print_status(const char *color, const char *bracket_text, const char *msg);
static void silence_kernel_logs(void);
static int do_mount(const char *source, const char *target, const char *fstype, unsigned long flags);
static int do_mount_opts(const char *source, const char *target, const char *fstype, unsigned long flags, const char *opts);
static void parse_cmdline(void);
static void setup_console_and_tty(void);
static void set_env(void);
static void set_hostname(void);
static void install_busybox_symlinks(void);
static void load_kernel_modules(void);
static void clear_screen(void);
static void print_banner(void);
static void run_init_scripts(void);
static void discover_services(void);
static struct service *find_service(const char *name);
static void start_service(struct service *svc);
static void stop_service(struct service *svc);
static void stop_all_services(void);
static void run_services(int runlevel);
static void set_runlevel(int level);
static void handle_service_command(const char *cmd);
static pid_t spawn_shell(const char *tty);
static void emergency_shell(void);
static void graceful_shutdown(void);
static int run_busybox(char *const argv[]);
static void setup_ipc(void);
static void update_status_file(void);
static void setup_devpts(void);
static void write_pid_file(const char *name, pid_t pid);
static void setup_loopback(void);
static void set_timezone(void);
static void create_standard_dirs(void);

static int telinit_main(int argc, char *argv[]);
static int instatus_main(int argc, char *argv[]);
static int in_service_main(int argc, char *argv[]);

static void install_own_symlinks(void) {
    char exe_path[256];
    
    ssize_t len = readlink("/proc/self/exe", exe_path, sizeof(exe_path) - 1);
    if (len != -1) {
        exe_path[len] = '\0';
    } else {
        strcpy(exe_path, "/sbin/init");
    }

    symlink(exe_path, "/sbin/telinit");
    if (symlink(exe_path, "/usr/bin/telinit") != 0 && errno != EEXIST) {
        do_log("warning: cannot create /usr/bin/telinit: %s\n", strerror(errno));
    }
    if (symlink(exe_path, "/usr/bin/in-status") != 0 && errno != EEXIST) {
        do_log("warning: cannot create /usr/bin/in-status: %s\n", strerror(errno));
    }
    if (symlink(exe_path, "/usr/bin/in-service") != 0 && errno != EEXIST) {
        do_log("warning: cannot create /usr/bin/in-service: %s\n", strerror(errno));
    }
}

int main(int argc, char *argv[]) {
    char *progname = strrchr(argv[0], '/');
    progname = progname ? progname + 1 : argv[0];

    if (strcmp(progname, "telinit") == 0) return telinit_main(argc, argv);
    if (strcmp(progname, "in-status") == 0) return instatus_main(argc, argv);
    if (strcmp(progname, "in-service") == 0) return in_service_main(argc, argv);

    if (getpid() != 1) {
        fprintf(stderr, "error: init must be run as PID 1\n");
        return 1;
    }

    clock_gettime(CLOCK_MONOTONIC, &boot_start);
    setup_signals();
    reboot(RB_DISABLE_CAD);

    /* базовые ФС */
    do_mount("proc", "/proc", "proc", MS_NOSUID | MS_NODEV | MS_NOEXEC);
    
    /* === ВАЖНО: ГЛУШИМ ЛОГИ ЯДРА ЧТОБЫ НЕ МУСОРИЛИ НА ЭКРАН === */
    silence_kernel_logs();

    do_mount("sysfs", "/sys", "sysfs", MS_NOSUID | MS_NODEV | MS_NOEXEC);
    do_mount("devtmpfs", "/dev", "devtmpfs", MS_NOSUID);
    
    mkdir("/run", 0755);
    do_mount("tmpfs", "/run", "tmpfs", MS_NOSUID | MS_NODEV | MS_NOEXEC);

    mkdir("/sys/fs/cgroup", 0755);
    do_mount("cgroup2", "/sys/fs/cgroup", "cgroup2", MS_NOSUID | MS_NODEV | MS_NOEXEC);

    mknod("/dev/fb0", S_IFCHR | 0666, makedev(29, 0));
    mknod("/dev/null", S_IFCHR | 0666, makedev(1, 3));
    mknod("/dev/zero", S_IFCHR | 0666, makedev(1, 5));
    mknod("/dev/tty", S_IFCHR | 0666, makedev(5, 0));

    mknod("/dev/tty1", S_IFCHR | 0666, makedev(4, 1));
    mknod("/dev/tty2", S_IFCHR | 0666, makedev(4, 2));

    /* /dev/pts монтируем */
    setup_devpts();

    mkdir("/var", 0755);
    mkdir("/var/log", 0755);

    /* создаём стандартные директории (/tmp, /run/lock и т.д.) */
    create_standard_dirs();

    do_log("================================\n");
    do_log("init started. COMBINE oneinit v0.9\n");

    /* пишем пид init в файл */
    write_pid_file("init", getpid());

    parse_cmdline();
    setup_ipc(); 

    if (current_runlevel == 0 || current_runlevel == 6) graceful_shutdown();
    if (current_runlevel == 1) {
        do_log("runlevel 1 requested. dropping to emergency shell.\n");
        emergency_shell();
        current_runlevel = 0;
        graceful_shutdown();
    }

    setup_console_and_tty();
    set_env();
    set_hostname();
    set_timezone();

    install_busybox_symlinks();
    load_kernel_modules();
    install_own_symlinks();

    /* поднимаем loopback */
    setup_loopback();

    /* очистка и отрисовка красивого интерфейса */
    clear_screen();
    print_banner();

    /* запуск служб с красивым выводом */
    run_init_scripts();

    /* Секьюрность */
    if (access("/usr/bin/doas", F_OK) == 0) {
        chown("/usr/bin/doas", 0, 0);
        chmod("/usr/bin/doas", 04755); 
    }
    if (access("/etc/doas.conf", F_OK) == 0) {
        chown("/etc/doas.conf", 0, 0);
        chmod("/etc/doas.conf", 0600);
    }

    update_status_file();

    struct timespec boot_end;
    clock_gettime(CLOCK_MONOTONIC, &boot_end);
    double elapsed = (boot_end.tv_sec - boot_start.tv_sec) + (boot_end.tv_nsec - boot_start.tv_nsec) / 1e9;
    
    printf("\n");
    print_status("1;36", " INFO ", "System initialized.");
    printf("         \033[1;30mBoot took %.2f seconds.\033[0m\n\n", elapsed);
    
    do_log("entering main init loop. runlevel = %d\n", current_runlevel);

    int fifo_fd = open("/run/initctl", O_RDWR | O_NONBLOCK);
    char cmd_buf[128];
    int cmd_len = 0;

    /* главный цикл */
    while (!shutdown_requested) {
        if (current_runlevel == 3 || current_runlevel == 5) {
            for (int i = 0; i < 2; i++) {
                if (shell_pids[i] == 0) {
                    shell_pids[i] = spawn_shell(tty_names[i]);
                }
            }
        }

        fd_set rfds;
        FD_ZERO(&rfds);
        if (fifo_fd >= 0) FD_SET(fifo_fd, &rfds);

        struct timeval tv;
        tv.tv_sec = 2;
        tv.tv_usec = 0;

        int retval = select((fifo_fd >= 0 ? fifo_fd + 1 : 0), &rfds, NULL, NULL, &tv);

        if (retval > 0 && fifo_fd >= 0 && FD_ISSET(fifo_fd, &rfds)) {
            char c;
            if (read(fifo_fd, &c, 1) == 1) {
                if (cmd_len == 0 && c >= '0' && c <= '6') {
                    set_runlevel(c - '0');
                } else if (c == '\n') {
                    cmd_buf[cmd_len] = '\0';
                    handle_service_command(cmd_buf);
                    cmd_len = 0;
                } else if (cmd_len < (int)sizeof(cmd_buf) - 1) {
                    cmd_buf[cmd_len++] = c;
                } else {
                    cmd_len = 0; /* сброс битых команд */
                }
            }
        }

        if (child_died) {
            child_died = 0;
            int status;
            pid_t p;
            while ((p = waitpid(-1, &status, WNOHANG)) > 0) {
                for (int i = 0; i < 2; i++) {
                    if (p == shell_pids[i]) shell_pids[i] = 0; 
                }
                for (int j = 0; j < service_count; j++) {
                    if (services[j].pid == p) {
                        char path[128];
                        snprintf(path, sizeof(path), "/run/%.100s.pid", services[j].name);
                        unlink(path);
                        services[j].pid = 0;
                        services[j].active = 0;
                        do_log("service %s exited unexpectedly\n", services[j].name);
                    }
                }
            }
        }
    }

    if (fifo_fd >= 0) close(fifo_fd);
    graceful_shutdown();
    return 0;
}

/* ================== УТИЛИТЫ УПРАВЛЕНИЯ ================== */

static int telinit_main(int argc, char *argv[]) {
    if (argc < 2) { printf("usage: telinit [0-6]\n"); return 1; }
    char cmd = argv[1][0];
    if (cmd < '0' || cmd > '6') { fprintf(stderr, "invalid runlevel\n"); return 1; }
    int fd = open("/run/initctl", O_WRONLY);
    if (fd < 0) return 1;
    write(fd, &cmd, 1);
    close(fd);
    return 0;
}

static int instatus_main(int argc, char *argv[]) {
    (void)argc; (void)argv;
    printf("\033[1;36m=== COMBINE v0.9 init status ===\033[0m\n");
    FILE *f = fopen("/run/init_status", "r");
    if (!f) return 1;
    char line[256];
    while(fgets(line, sizeof(line), f)) printf("%s", line);
    fclose(f);
    printf("\033[1;36m==============================\033[0m\n");
    return 0;
}

static int in_service_main(int argc, char *argv[]) {
    if (argc < 2) {
        printf("usage: in-service <start|stop|restart|list> [service]\n");
        return 1;
    }
    int fd = open("/run/initctl", O_WRONLY);
    if (fd < 0) {
        perror("in-service: /run/initctl");
        return 1;
    }
    char cmd[128];
    if (argc >= 3) snprintf(cmd, sizeof(cmd), "%s %s\n", argv[1], argv[2]);
    else snprintf(cmd, sizeof(cmd), "%s\n", argv[1]);
    if (write(fd, cmd, strlen(cmd)) < 0) {
        perror("in-service: write");
        close(fd);
        return 1;
    }
    close(fd);
    usleep(200000); /* даём init время обновить /run/init_status */

    FILE *f = fopen("/run/init_status", "r");
    if (!f) return 1;
    char line[256];
    int in_services = 0;
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, "Services:", 9) == 0) in_services = 1;
        if (in_services) printf("%s", line);
    }
    fclose(f);
    return 0;
}

/* ================== ВНУТРЯНКА INIT ================== */

/* глушим ядро, чтобы printk не мусорил поверх нашего баннера */
static void silence_kernel_logs(void) {
    int fd = open("/proc/sys/kernel/printk", O_WRONLY);
    if (fd >= 0) {
        write(fd, "3 4 1 3\n", 8); /* оставляем только критические ошибки ядра */
        close(fd);
    }
}

/* красивый вывод статуса + запись в лог файл */
static void print_status(const char *color, const char *bracket_text, const char *msg) {
    printf("[\033[%sm%s\033[0m] %s\n", color, bracket_text, msg);
    fflush(stdout); /* обязательно выталкиваем на экран перед возможным скриптом */
    do_log("[%s] %s\n", bracket_text, msg); 
}

/* запись ТОЛЬКО в файл, чтобы не дублировать на экране и не мусорить в kmsg */
static void do_log(const char *fmt, ...) {
    va_list args;
    FILE *f = fopen("/var/log/init.log", "a");
    if (f) {
        time_t t = time(NULL);
        struct tm *tm = localtime(&t);
        fprintf(f, "[%02d:%02d:%02d] init: ", tm->tm_hour, tm->tm_min, tm->tm_sec);
        va_start(args, fmt);
        vfprintf(f, fmt, args);
        va_end(args);
        fclose(f);
    }
}

static void clear_screen(void) {
    write(STDOUT_FILENO, "\033[2J\033[H", 7);
}

static void print_banner(void) {
    printf("\033[0;34m========\033[1;34m========\033[0;36m========\033[1;36m================\033[0m\n\n");
    printf("\033[1;36m  COMBINE v0.9 \033[1;30m//\033[1;36m oneinit v0.9\033[0m\n\n");
    printf("\033[1;37m  C O M B I N E   L i n u x\033[0m\n");
    printf("\033[1;30m  glibc + GNU coreutils\033[0m\n\n");
    printf("  welcome!\n");
    printf("\033[0;34m========\033[1;34m========\033[0;36m========\033[1;36m================\033[0m\n\n");
}

static int cmp_service(const void *a, const void *b) {
    const struct service *sa = a, *sb = b;
    return sa->order - sb->order;
}

/* Имя сервиса и порядок берём из имени файла: S20-network, D50-x11, K50-x11 */
static const char *service_name_from_file(const char *file, int *order, int *daemon) {
    const char *p = file;
    *daemon = 0;
    *order = 0;
    if (*p == 'S' || *p == 'D' || *p == 'K') {
        *daemon = (*p == 'D');
        p++;
    }
    while (isdigit((unsigned char)*p)) {
        *order = *order * 10 + (*p - '0');
        p++;
    }
    if (*p == '-' || *p == '.') p++;
    return p;
}

static struct service *find_service(const char *name) {
    for (int i = 0; i < service_count; i++) {
        if (strcmp(services[i].name, name) == 0) return &services[i];
    }
    return NULL;
}

static void discover_services(void) {
    DIR *d = opendir("/etc/init.d");
    if (!d) return;
    struct dirent *de;

    /* стартовые скрипты */
    while ((de = readdir(d)) != NULL) {
        const char *n = de->d_name;
        if (n[0] == '.' || n[0] == 'K') continue;
        if (!(n[0] == 'S' || n[0] == 'D' || isdigit((unsigned char)n[0]))) continue;

        int order = 0, daemon = 0;
        const char *name = service_name_from_file(n, &order, &daemon);
        if (!*name) continue;

        char path[512];
        snprintf(path, sizeof(path), "/etc/init.d/%s", n);
        if (access(path, X_OK) != 0) continue;

        struct service *svc = find_service(name);
        if (!svc) {
            if (service_count >= MAX_SERVICES) continue;
            svc = &services[service_count++];
            memset(svc, 0, sizeof(*svc));
            snprintf(svc->name, sizeof(svc->name), "%s", name);
            svc->order = order;
            svc->levels = (1 << 3) | (1 << 5); /* по умолчанию: консоль и графика */
            svc->daemon = daemon;
        }
        snprintf(svc->start_path, sizeof(svc->start_path), "/etc/init.d/%.170s", n);

        /* <name>.levels: цифры 0-6 задают уровни, на которых сервис нужен */
        char cfg[256];
        snprintf(cfg, sizeof(cfg), "/etc/init.d/%s.levels", name);
        FILE *f = fopen(cfg, "r");
        if (f) {
            svc->levels = 0;
            int ch;
            while ((ch = fgetc(f)) != EOF) {
                if (ch >= '0' && ch <= '6') svc->levels |= 1 << (ch - '0');
            }
            fclose(f);
        }
    }

    /* стоп-скрипты K##-<name> */
    rewinddir(d);
    while ((de = readdir(d)) != NULL) {
        const char *n = de->d_name;
        if (n[0] != 'K' || n[1] == '.') continue;
        int order = 0, daemon = 0;
        const char *name = service_name_from_file(n, &order, &daemon);
        struct service *svc = find_service(name);
        if (!svc) continue;
        char path[512];
        snprintf(path, sizeof(path), "/etc/init.d/%s", n);
        if (access(path, X_OK) == 0)
            snprintf(svc->stop_path, sizeof(svc->stop_path), "/etc/init.d/%.170s", n);
    }
    closedir(d);

    qsort(services, service_count, sizeof(struct service), cmp_service);
    for (int i = 0; i < service_count; i++) {
        do_log("service %s: %s (levels=%x, %s)\n", services[i].name,
               services[i].start_path, services[i].levels,
               services[i].daemon ? "daemon" : "oneshot");
    }
}

static void start_service(struct service *svc) {
    if (!svc || !svc->start_path[0] || svc->active) return;
    svc->last_status = -1;
    print_status("1;33", "  WAIT  ", svc->name);

    pid_t pid = fork();
    if (pid == 0) {
        setsid();
        if (svc->daemon) {
            int fd = open("/var/log/services.log", O_WRONLY | O_CREAT | O_APPEND, 0644);
            if (fd >= 0) {
                dup2(fd, STDOUT_FILENO);
                dup2(fd, STDERR_FILENO);
                if (fd > 2) close(fd);
            }
        }
        execl(svc->start_path, svc->start_path, "start", (char *)NULL);
        _exit(127);
    }
    if (pid < 0) {
        print_status("1;31", "  FAIL  ", svc->name);
        return;
    }

    if (svc->daemon) {
        svc->pid = pid;
        svc->active = 1;
        svc->last_status = 0;
        write_pid_file(svc->name, pid);
        print_status("1;32", "  OK   ", svc->name);
    } else {
        int status = 0;
        while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
        svc->last_status = WIFEXITED(status) ? WEXITSTATUS(status) : -1;
        if (svc->last_status == 0) {
            svc->active = 1;
            svc->pid = 0;
            print_status("1;32", "  OK   ", svc->name);
        } else {
            print_status("1;31", "  FAIL  ", svc->name);
            do_log("service %s failed with exit code %d\n", svc->name, svc->last_status);
        }
    }
    update_status_file();
}

static void stop_service(struct service *svc) {
    if (!svc || !svc->active) return;
    if (svc->stop_path[0]) {
        pid_t pid = fork();
        if (pid == 0) {
            setsid();
            execl(svc->stop_path, svc->stop_path, "stop", (char *)NULL);
            _exit(127);
        }
        if (pid > 0) {
            int status = 0;
            while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
        }
    }
    if (svc->pid > 0) {
        kill(-svc->pid, SIGTERM);
        for (int i = 0; i < 20; i++) {
            if (waitpid(svc->pid, NULL, WNOHANG) == svc->pid) break;
            usleep(100000);
        }
        if (kill(-svc->pid, 0) == 0) {
            kill(-svc->pid, SIGKILL);
            waitpid(svc->pid, NULL, 0);
        }
        char path[128];
        snprintf(path, sizeof(path), "/run/%.100s.pid", svc->name);
        unlink(path);
    }
    svc->active = 0;
    svc->pid = 0;
    do_log("service %s stopped\n", svc->name);
    update_status_file();
}

static void stop_all_services(void) {
    for (int i = service_count - 1; i >= 0; i--) stop_service(&services[i]);
}

static void run_services(int runlevel) {
    for (int i = 0; i < service_count; i++) {
        if (!(services[i].levels & (1 << runlevel))) continue;
        if (!services[i].active) start_service(&services[i]);
    }
}

static void set_runlevel(int level) {
    if (level == current_runlevel) return;
    current_runlevel = level;
    update_status_file();
    do_log("runlevel change: %d\n", level);

    if (level == 0 || level == 6) { shutdown_requested = 1; return; }
    if (level == 1) {
        kill(-1, SIGTERM);
        emergency_shell();
        shutdown_requested = 1;
        return;
    }
    for (int i = service_count - 1; i >= 0; i--) {
        if (!(services[i].levels & (1 << level))) stop_service(&services[i]);
    }
    run_services(level);
}

static void handle_service_command(const char *cmd) {
    if (!cmd || !*cmd) return;
    if (strcmp(cmd, "list") == 0) { update_status_file(); return; }

    char action[16], name[48];
    if (sscanf(cmd, "%15s %47s", action, name) != 2) {
        do_log("bad in-service command: %s\n", cmd);
        return;
    }
    struct service *svc = find_service(name);
    if (!svc) {
        do_log("unknown service: %s\n", name);
        return;
    }
    if (strcmp(action, "start") == 0) start_service(svc);
    else if (strcmp(action, "stop") == 0) stop_service(svc);
    else if (strcmp(action, "restart") == 0) { stop_service(svc); start_service(svc); }
    else do_log("unknown in-service action: %s\n", action);
    update_status_file();
}

static void run_init_scripts(void) {
    discover_services();
    run_services(current_runlevel);
    update_status_file();
}

static void setup_devpts(void) {
    print_status("1;33", "  WAIT  ", "mounting /dev/pts");

    /* создаём точку монтирования если её ещё нет */
    if (mkdir("/dev/pts", 0755) != 0 && errno != EEXIST) {
        do_log("warning: cannot mkdir /dev/pts: %s\n", strerror(errno));
    }

    const char *opts = "ptmxmode=0666,gid=5,mode=0620,newinstance";
    if (mount("devpts", "/dev/pts", "devpts",
              MS_NOSUID | MS_NOEXEC, opts) != 0) {
        if (errno == EBUSY) {
            /* Уже смонтировано — попробуем без newinstance (старые ядра) */
            do_log("devpts busy, retrying without newinstance\n");
            mount("devpts", "/dev/pts", "devpts",
                  MS_NOSUID | MS_NOEXEC, "ptmxmode=0666,gid=5,mode=0620");
        } else {
            do_log("mount fail: devpts on /dev/pts: %s\n", strerror(errno));
            print_status("1;31", "  FAIL  ", "failed to mount /dev/pts");
            return;
        }
    }

    unlink("/dev/ptmx"); /* убираем старый chardev если был */
    if (symlink("/dev/pts/ptmx", "/dev/ptmx") != 0 && errno != EEXIST) {
        do_log("ptmx symlink failed (%s), creating chardev\n", strerror(errno));
        mknod("/dev/ptmx", S_IFCHR | 0666, makedev(5, 2));
        chown("/dev/ptmx", 0, 5); /* root:tty */
        chmod("/dev/ptmx", 0666);
    }

    print_status("1;32", "   OK   ", "/dev/pts mounted, /dev/ptmx ready");
    do_log("devpts mounted with opts: %s\n", opts);
}

static void write_pid_file(const char *name, pid_t pid) {
    char path[128];
    snprintf(path, sizeof(path), "/run/%s.pid", name);
    FILE *f = fopen(path, "w");
    if (f) {
        fprintf(f, "%d\n", (int)pid);
        fclose(f);
        do_log("pid file written: %s = %d\n", path, (int)pid);
    } else {
        do_log("warning: cannot write pid file %s: %s\n", path, strerror(errno));
    }
}

static void setup_loopback(void) {
    print_status("1;33", "  WAIT  ", "bringing up loopback interface");

    /* ip link set lo up */
    pid_t pid = fork();
    if (pid == 0) {
        execl("/bin/busybox", "busybox", "ip", "link", "set", "lo", "up", (char *)NULL);
        /* фолбэк через ifconfig если ip недоступен */
        execl("/bin/busybox", "busybox", "ifconfig", "lo", "up", (char *)NULL);
        _exit(1);
    }
    int status;
    waitpid(pid, &status, 0);

    /* ip addr add 127.0.0.1/8 dev lo */
    pid = fork();
    if (pid == 0) {
        execl("/bin/busybox", "busybox", "ip", "addr", "add",
              "127.0.0.1/8", "dev", "lo", (char *)NULL);
        execl("/bin/busybox", "busybox", "ifconfig", "lo",
              "127.0.0.1", "netmask", "255.0.0.0", (char *)NULL);
        _exit(1);
    }
    waitpid(pid, &status, 0);

    if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
        print_status("1;32", "   OK   ", "loopback interface is up");
    } else {
        /* Не фатально — логируем и идём дальше */
        print_status("1;33", "  WARN  ", "loopback setup returned non-zero (may already be up)");
    }
    do_log("loopback interface configured\n");
}

static void set_timezone(void) {
    FILE *f = fopen("/etc/timezone", "r");
    if (!f) {
        do_log("no /etc/timezone found, using UTC\n");
        return;
    }

    char tz[128] = {0};
    if (fgets(tz, sizeof(tz), f)) {
        tz[strcspn(tz, "\r\n")] = '\0';
    }
    fclose(f);

    if (tz[0] == '\0') {
        do_log("empty /etc/timezone, using UTC\n");
        return;
    }

    /* выставляем tz в виде :/usr/share/zoneinfo/Region/City */
    char tz_env[160];
    snprintf(tz_env, sizeof(tz_env), "/usr/share/zoneinfo/%s", tz);
    if (access(tz_env, F_OK) == 0) {
        char tz_val[164];
        snprintf(tz_val, sizeof(tz_val), ":%s", tz_env);
        setenv("TZ", tz_val, 1);
    } else {
        /* фолбэк: выставляем имя напрямую (posix-формат если zoneinfo нет) */
        setenv("TZ", tz, 1);
    }
    tzset();
    do_log("timezone set to: %s\n", tz);
}

static void create_standard_dirs(void) {
    /* /tmp — нужен практически всем */
    if (mkdir("/tmp", 01777) != 0 && errno != EEXIST)
        do_log("warning: cannot mkdir /tmp: %s\n", strerror(errno));
    chmod("/tmp", 01777); /* sticky bit */

    /* /run/lock — lockfile-совместимость */
    if (mkdir("/run/lock", 01777) != 0 && errno != EEXIST)
        do_log("warning: cannot mkdir /run/lock: %s\n", strerror(errno));
    chmod("/run/lock", 01777);

    /* /run/dropbear — dropbear кладёт сюда host keys и pid */
    if (mkdir("/run/dropbear", 0700) != 0 && errno != EEXIST)
        do_log("warning: cannot mkdir /run/dropbear: %s\n", strerror(errno));

    /* /var/run -> /run (symlink для совместимости со старыми скриптами) */
    if (symlink("/run", "/var/run") != 0 && errno != EEXIST)
        do_log("note: /var/run symlink: %s\n", strerror(errno));

    /* /var/tmp — временные файлы, переживающие перезагрузку (если /var на диске) */
    if (mkdir("/var/tmp", 01777) != 0 && errno != EEXIST)
        do_log("warning: cannot mkdir /var/tmp: %s\n", strerror(errno));

    do_log("standard directories created\n");
}

static int do_mount_opts(const char *source, const char *target,
                         const char *fstype, unsigned long flags,
                         const char *opts) {
    if (mount(source, target, fstype, flags, opts) != 0 && errno != EBUSY) {
        do_log("mount fail: %s on %s (%s)\n", source, target, strerror(errno));
        return -1;
    }
    return 0;
}

static void setup_ipc(void) {
    unlink("/run/initctl");
    if (mkfifo("/run/initctl", 0600) != 0) do_log("failed to create /run/initctl\n");
}

static void update_status_file(void) {
    FILE *f = fopen("/run/init_status", "w");
    if (f) {
        fprintf(f, "PID 1: running\nCurrent Runlevel: %d\n", current_runlevel);
        fprintf(f, "Services:\n");
        for (int i = 0; i < service_count; i++) {
            fprintf(f, "  %-16s %s (exit %d)", services[i].name,
                    services[i].active ? "active" : "stopped", services[i].last_status);
            if (services[i].pid > 0) fprintf(f, " (pid %d)", (int)services[i].pid);
            fprintf(f, "\n");
        }
        fclose(f);
    }
}

static void sig_handler(int sig) {
    if (sig == SIGCHLD) child_died = 1;
    else if (sig == SIGTERM || sig == SIGUSR1) { shutdown_requested = 1; current_runlevel = 0; }
    else if (sig == SIGINT) { shutdown_requested = 1; current_runlevel = 6; }
}

static void setup_signals(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = sig_handler;
    sa.sa_flags = SA_RESTART | SA_NOCLDSTOP; 
    sigaction(SIGCHLD, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGINT, &sa, NULL); 
    sigaction(SIGUSR1, &sa, NULL); 
    signal(SIGQUIT, SIG_IGN);
    signal(SIGTSTP, SIG_IGN);
    signal(SIGHUP, SIG_IGN);
    signal(SIGPIPE, SIG_IGN);
}

static void parse_cmdline(void) {
    FILE *f = fopen("/proc/cmdline", "r");
    if (!f) return;
    char line[1024];
    if (fgets(line, sizeof(line), f)) {
        if (strstr(line, "runlevel=0") || strstr(line, " 0")) current_runlevel = 0;
        else if (strstr(line, "runlevel=1") || strstr(line, " single") || strstr(line, " 1")) current_runlevel = 1;
        else if (strstr(line, "runlevel=3") || strstr(line, " 3")) current_runlevel = 3;
        else if (strstr(line, "runlevel=5") || strstr(line, " 5")) current_runlevel = 5; 
        else if (strstr(line, "runlevel=6") || strstr(line, " 6")) current_runlevel = 6;
    }
    fclose(f);
}

static void graceful_shutdown(void) {
    printf("\n\033[1;31m*** INITIATING SHUTDOWN SEQUENCE ***\033[0m\n");
    printf("stopping services...\n");
    stop_all_services();
    printf("sending SIGTERM to all processes...\n");
    kill(-1, SIGTERM);
    sync(); 
    sleep(2); 

    printf("sending SIGKILL...\n");
    kill(-1, SIGKILL);
    sync();
    
    printf("unmounting filesystems...\n");
    pid_t pid = fork();
    if (pid == 0) {
        execl("/bin/busybox", "busybox", "umount", "-a", "-r", (char *)NULL);
        _exit(1);
    }
    waitpid(pid, NULL, 0);

    if (current_runlevel == 6) {
        printf("rebooting system...\n");
        reboot(RB_AUTOBOOT);
    } else {
        printf("powering off...\n");
        reboot(RB_POWER_OFF);
    }
    while(1) pause(); 
}

static void emergency_shell(void) {
    printf("\033[1;31mDROPPING TO EMERGENCY SHELL!\033[0m\n");
    pid_t pid = fork();
    if (pid == 0) {
        int fd = open("/dev/tty1", O_RDWR);
        if (fd >= 0) {
            dup2(fd, STDIN_FILENO); dup2(fd, STDOUT_FILENO); dup2(fd, STDERR_FILENO);
            if (fd > 2) close(fd);
        }
        setenv("PS1", "(emergency) # ", 1);
        execl("/bin/busybox", "busybox", "sh", (char *)NULL);
        _exit(1); 
    }
    waitpid(pid, NULL, 0);
}

static int do_mount(const char *source, const char *target, const char *fstype, unsigned long flags) {
    if (mount(source, target, fstype, flags, NULL) != 0 && errno != EBUSY) {
        do_log("mount fail: %s on %s\n", source, target);
        return -1;
    }
    return 0;
}

static void setup_console_and_tty(void) {
    int fd = open("/dev/tty1", O_RDWR);
    if (fd >= 0) {
        pid_t pid = fork();
        if (pid == 0) {
            dup2(fd, STDIN_FILENO); dup2(fd, STDOUT_FILENO);
            execl("/bin/busybox", "busybox", "stty", "sane", (char *)NULL);
            _exit(1);
        }
        waitpid(pid, NULL, 0);
        dup2(fd, STDIN_FILENO); dup2(fd, STDOUT_FILENO); dup2(fd, STDERR_FILENO);
        ioctl(fd, TIOCSCTTY, 1);
        if (fd > 2) close(fd);
    }
}

static void set_env(void) {
    setenv("PATH", "/bin:/sbin:/usr/bin:/usr/sbin", 1);
    setenv("HOME", "/", 1);
    setenv("SSL_CERT_FILE", "/etc/ssl/certs/ca-certificates.crt", 1);
}

static void set_hostname(void) {
    char hname[256] = "combine";
    FILE *f = fopen("/etc/hostname", "r");
    if (f) {
        if (fgets(hname, sizeof(hname), f)) hname[strcspn(hname, "\r\n")] = 0;
        fclose(f);
    }
    if (hname[0] == '\0') strcpy(hname, "combine");
    sethostname(hname, strlen(hname));
}

static void install_busybox_symlinks(void) {
    int pfd[2];
    if (pipe(pfd) < 0) {
        do_log("error: cannot create pipe for busybox setup: %s\n", strerror(errno));
        return;
    }

    print_status("1;33", "  WAIT  ", "installing busybox symlinks");

    pid_t pid = fork();
    if (pid == 0) {
        close(pfd[0]);
        dup2(pfd[1], STDOUT_FILENO);
        close(pfd[1]);
        execl("/bin/busybox", "busybox", "--list", (char *)NULL);
        _exit(1);
    }

    close(pfd[1]);
    FILE *stream = fdopen(pfd[0], "r");
    if (stream) {
        char cmd[128];
        char link_path[256];
        
        while (fgets(cmd, sizeof(cmd), stream)) {
            cmd[strcspn(cmd, "\r\n")] = 0;
            if (cmd[0] == '\0') continue;

            snprintf(link_path, sizeof(link_path), "/bin/%s", cmd);

            if (symlink("/bin/busybox", link_path) != 0 && errno != EEXIST) {
                do_log("warning: failed to link %s: %s\n", link_path, strerror(errno));
            }
        }
        fclose(stream);
    }
    close(pfd[0]);
    waitpid(pid, NULL, 0);

    print_status("1;32", "   OK   ", "all busybox commands linked to /bin");
}

static void load_kernel_modules(void) {
    struct utsname uts;
    if (uname(&uts) != 0) {
        do_log("failed to get kernel version for modules\n");
        return;
    }

    print_status("1;33", "  WAIT  ", "loading kernel modules");

    pid_t pid = fork();
    if (pid == 0) {
        /* virtio_pci must come before virtio_net: it is the PCI transport,
         * virtio_net is only the network driver that binds to it. */
        execl("/bin/busybox", "busybox", "modprobe", "-a",
              "bochs", "evdev", "psmouse", "virtio_pci", "virtio_net", "e1000", (char *)NULL);
        _exit(1);
    }
    
    int status;
    waitpid(pid, &status, 0);

    if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
        print_status("1;32", "   OK   ", "kernel modules loaded");
    } else {
        print_status("1;31", "  FAIL  ", "failed to load kernel modules");
    }
}

static pid_t spawn_shell(const char *tty) {
    pid_t pid = fork();
    if (pid == 0) {
        setsid();
        usleep(100000);
        char devpath[32];
        snprintf(devpath, sizeof(devpath), "/dev/%s", tty);
        execl("/bin/busybox", "busybox", "getty", "38400", tty, (char *)NULL);
        
        int fd = open(devpath, O_RDWR);
        if (fd >= 0) {
            ioctl(fd, TIOCSCTTY, 1);
            dup2(fd, STDIN_FILENO); dup2(fd, STDOUT_FILENO); dup2(fd, STDERR_FILENO);
            if (fd > 2) close(fd);
            execl("/bin/busybox", "busybox", "login", "-p", (char *)NULL);
            execl("/bin/sh", "sh", (char *)NULL);
        }
        _exit(1);
    }
    return pid;
}

static int run_busybox(char *const argv[]) {
    pid_t pid = fork();
    if (pid == 0) {
        execv(argv[0], argv);
        _exit(1);
    }
    int status;
    waitpid(pid, &status, 0);
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}
