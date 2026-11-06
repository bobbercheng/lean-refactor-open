/* Prefix-reuse compile server (postfast, 2026-11-05): process primitives for driver.lean.
   Two builds per toolchain:
     native (preferred): driver.lean compiled with `lean -c`, linked with this file built with -DPSRV_NATIVE against the toolchain's shared
       libraries (as bin/lean is). The compiled code calls the `@[extern]` names below with their unboxed signatures.
     dynlib (fallback): `lean --load-dynlib=psrv.so -M<mb> --run driver.lean`. The IR interpreter resolves the `@[extern]` declarations of
       an interpreted file through the symbols `l_<mangled name>___boxed` (every argument owned and boxed, the world last). This mode
       imports Lean twice (the driver's own `import Lean` and the prefix's imports), ~1.7 GB more private memory per server.

   PrefixServer.forkInto (fifo : String) : IO UInt32
     fork(); the child opens `fifo` for writing (the client holds the read end open already, so a missing reader means the client
     gave up: the child exits), makes it fd 1, asks to be killed when the server dies, restores SIGCHLD, and installs a fresh task
     manager (the parent's worker threads do not exist in the child); returns 0 in the child and the child's pid in the parent.
   PrefixServer.exitNow (code : UInt32) : IO Unit
     flush stdio and _exit (no finalizers: the child's inherited task manager references threads that do not exist).
   PrefixServer.ignoreSigchld : IO Unit
     the kernel reaps the children (the client sees a child's end as the FIFO's hang-up). */
#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <unistd.h>

/* A child that leaves through exit() (IO.Process.exit: e.g. runAndReport after `maxErrors` errors) instead of exitNow: flush what
   was printed, append the sentinel line {"__psrv__":"exit","code":N} (preceded by a newline the client strips again) and _exit with
   the same status, as `lean` would have exited. */
static void psrv_on_exit(int status, void * arg) {
    (void)arg;
    fflush(stdout);
    char buf[96];
    int n = snprintf(buf, sizeof buf, "\n{\"__psrv__\":\"exit\",\"code\":%d}\n", status);
    if (n > 0) {
        ssize_t r = write(1, buf, (size_t)n);
        (void)r;
    }
    _exit(status);
}

LEAN_EXPORT lean_object * psrv_fork_into(lean_object * path, lean_object * w) {
    (void)w;
    fflush(stdout);
    fflush(stderr);
    pid_t parent = getpid();
    pid_t pid = fork();
    if (pid < 0) {
        int e = errno;
        lean_dec(path);
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(strerror(e))));
    }
    if (pid == 0) {
        prctl(PR_SET_PDEATHSIG, SIGKILL);
        if (getppid() != parent)
            _exit(96);
        int fd = open(lean_string_cstr(path), O_WRONLY | O_NONBLOCK);
        if (fd < 0)
            _exit(97);
        int fl = fcntl(fd, F_GETFL);
        if (fl < 0 || fcntl(fd, F_SETFL, fl & ~O_NONBLOCK) < 0 || dup2(fd, 1) < 0)
            _exit(98);
        close(fd);
        signal(SIGCHLD, SIG_DFL);
        on_exit(psrv_on_exit, NULL);
        lean_init_task_manager();
    }
    lean_dec(path);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)pid));
}

LEAN_EXPORT lean_object * psrv_exit_now(uint32_t code, lean_object * w) {
    (void)w;
    fflush(stdout);
    fflush(stderr);
    _exit((int)code);
}

LEAN_EXPORT lean_object * psrv_ignore_sigchld(lean_object * w) {
    (void)w;
    signal(SIGCHLD, SIG_IGN);
    return lean_io_result_mk_ok(lean_box(0));
}

#ifndef PSRV_NATIVE
extern lean_object * lean_internal_set_max_memory(size_t max, lean_object * w);   /* Lean runtime (libleanshared) */

LEAN_EXPORT lean_object * l_PrefixServer_setMaxMemoryRt___boxed(lean_object * max, lean_object * w) {
    return lean_internal_set_max_memory(lean_unbox_usize(max), w);
}

LEAN_EXPORT lean_object * l_PrefixServer_forkInto___boxed(lean_object * path, lean_object * w) {
    return psrv_fork_into(path, w);
}

LEAN_EXPORT lean_object * l_PrefixServer_exitNow___boxed(lean_object * code, lean_object * w) {
    return psrv_exit_now(lean_unbox_uint32(code), w);
}

LEAN_EXPORT lean_object * l_PrefixServer_ignoreSigchld___boxed(lean_object * w) {
    return psrv_ignore_sigchld(w);
}

LEAN_EXPORT lean_object * l_PrefixServer_ignoreSigchld(lean_object * w) {
    return psrv_ignore_sigchld(w);
}
#endif
