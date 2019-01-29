/* -*- c-file-style: "java"; indent-tabs-mode: nil; tab-width: 4; fill-column: 78 -*-
 *
 * distcc -- A simple distributed compiler system
 *
 * Copyright (C) 2002, 2003, 2004 by Martin Pool
 * Copyright 2007 Google Inc.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
 * USA.
 */

/*
 * Send a compilation request to a remote server.
 */


#include <config.h>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>
#include <limits.h>

#include <sys/types.h>
#include <sys/time.h>

#include "distcc.h"
#include "trace.h"
#include "rpc.h"
#include "exitcode.h"
#include "util.h"
#include "clinet.h"
#include "hosts.h"
#include "exec.h"
#include "lock.h"
#include "compile.h"
#include "bulk.h"
#ifdef HAVE_GSSAPI
#include "auth.h"

/* Global security context in case confidentiality/integrity */
/* type services are needed in the future. */
extern gss_ctx_id_t distcc_ctx_handle;
#endif

/*
 * TODO: If cpp finishes early and fails then perhaps break out of
 * trying to connect.
 *
 * TODO: If we abort, perhaps kill the SSH child rather than closing
 * the socket.  Closing while a lot of stuff has been written through
 * might make us block until the other side reads all the data.
 */

/**
 * Open a connection using either a TCP socket or SSH.  Return input
 * and output file descriptors (which may or may not be different.)
 **/
static int dcc_remote_connect(struct dcc_hostdef *host,
                              int *to_net_fd,
                              int *from_net_fd,
                              pid_t *ssh_pid)
{
    int ret;

    if (host->mode == DCC_MODE_TCP) {
        *ssh_pid = 0;
        if ((ret = dcc_connect_by_name(host->hostname, host->port,
                                       to_net_fd)) != 0)
            return ret;
        *from_net_fd = *to_net_fd;
        return 0;
    } else if (host->mode == DCC_MODE_SSH) {
        if ((ret = dcc_ssh_connect(NULL, host->user, host->hostname,
                                   host->ssh_command,
                                   from_net_fd, to_net_fd,
                                   ssh_pid)))
            return ret;
        return 0;
    } else {
        rs_log_crit("impossible host mode");
        return EXIT_DISTCC_FAILED;
    }
}


static int dcc_wait_for_cpp(pid_t cpp_pid,
                            int *status,
                            const char *input_fname)
{
    int ret;

    if (cpp_pid) {
        dcc_note_state(DCC_PHASE_CPP, NULL, NULL, DCC_LOCAL);
        /* Wait for cpp to finish (if not already done), check the
         * result, then send the .i file */

        if ((ret = dcc_collect_child("cpp", cpp_pid, status, timeout_null_fd)))
            return ret;

        /* Although cpp failed, there is no need to try running the command
         * locally, because we'd presumably get the same result.  Therefore
         * critique the command and log a message and return an indication
         * that compilation is complete. */
        if (dcc_critique_status(*status, "cpp", input_fname, dcc_hostdef_local, 0))
            return 0;
    }
    return 0;
}


/* Send a request across to the already-open server.
 *
 * CPP_PID is the PID of the preprocessor running in the background.
 * We wait for it to complete before reading its output.
 */
static int
dcc_send_header(int net_fd,
                char **argv,
                struct dcc_hostdef *host)
{
    int ret;

    tcp_cork_sock(net_fd, 1);

    if ((ret = dcc_x_req_header(net_fd, host->protover)))
        return ret;
    if (host->cpp_where == DCC_CPP_ON_SERVER) {
        if ((ret = dcc_x_cwd(net_fd)))
            return ret;
    }
    if ((ret = dcc_x_argv(net_fd, "ARGC", "ARGV", argv)))
        return ret;

    return 0;
}

static int
dcc_get_precompiled_header_path(const char *header_list_fname, char precompiled_header_path[PATH_MAX]) {
    int ret;
    int fd;
    off_t file_size;

    precompiled_header_path[0] = 0;
    if (header_list_fname == NULL) {
        return 0;
    }

    if ((ret = dcc_open_read(header_list_fname, &fd, &file_size))) {
        return ret;
    }

    char *data = (char *)malloc(file_size + 1);
    if (data == NULL) {
        dcc_close(fd);
        return EXIT_OUT_OF_MEMORY;
    }

    if ((ret = dcc_readx(fd, data, file_size))) {
        free(data);
        dcc_close(fd);
        return ret;
    }
    data[file_size] = 0;

    const char precompiled_preprocess[] = "#pragma GCC pch_preprocess \"";
    const char *begin = strstr(data, precompiled_preprocess);
    if (begin) {
        begin += strlen(precompiled_preprocess);
        const char *end = strchr(begin, '"');
        if (!end || end - begin >= PATH_MAX) {
            free(data);
            dcc_close(fd);
            return EXIT_DISTCC_FAILED;
        }
        strncpy(precompiled_header_path, begin, end - begin);
        precompiled_header_path[end - begin] = 0;
    }

    free(data);
    dcc_close(fd);
    return 0;
}

/**
 * Sends precompiled header path and sends precompiled header itself if need.
 *
 * PCHP: precompiled header path on disk; it should be present on distccd agent
 * PCHR:
 *      0 - if precompiled header is present on distccd agent or we do not need it at all
 *      1 - if precompiled header is absent on distccd agent and we should send it
 * PCHF: precompiled header file itself
 **/
static int
try_exchange_precompiled_header(int to_net_fd, int from_net_fd, char *input_fname, int *status,
                                const char *header_list_fname, pid_t header_list_pid) {
    int ret;
    if ((ret = dcc_wait_for_cpp(header_list_pid, status, input_fname))) {
        return ret;
    }

    char precompiled_header_path[PATH_MAX] = {0};
    if ((ret = dcc_get_precompiled_header_path(header_list_fname, precompiled_header_path))) {
        return ret;
    }

    /* expect that precompiled header is placed on tmp dir */
    /* TODO: may be such limitation too strict? */
    if (precompiled_header_path[0] && strncmp(precompiled_header_path, "/tmp/", 5)) {
        rs_log_warning("expect precompiled header in /tmp dir, got %s", precompiled_header_path);
        precompiled_header_path[0] = 0;
    }

    if ((ret = dcc_x_token_string(to_net_fd, "PCHP", precompiled_header_path))) {
        return ret;
    }

    unsigned precompiled_header_required;
    if ((ret = dcc_r_token_int(from_net_fd, "PCHR", &precompiled_header_required))) {
        return ret;
    }

    if (precompiled_header_required) {
        if ((ret = dcc_x_file(to_net_fd, precompiled_header_path, "PCHF", DCC_COMPRESS_LZO1X, NULL))) {
            return ret;
        }
    }
    return 0;
}
/**
 * Pass a compilation across the network.
 *
 * When this function is called, the preprocessor has already been
 * started in the background.  It may have already completed, or it
 * may still be running.  The goal is that preprocessing will overlap
 * with setting up the network connection, which may take some time
 * but little CPU.
 *
 * If this function fails, compilation will be retried on the local
 * machine.
 *
 * @param argv Compiler command to run.
 *
 * @param cpp_fname Filename of preprocessed source. May not be complete yet,
 * depending on @p cpp_pid.
 *
 * @param header_list_fname Filename of list with used headers.
 * May not be complete yet, depending on @p header_list_pid.
 *
 * @param files If we are doing preprocessing on the server, the names of
 * all the files needed; otherwise, NULL.
 *
 * @param output_fname File that the object code should be delivered to.
 *
 * @param cpp_pid If nonzero, the pid of the preprocessor. Must be
 * allowed to complete before we send the input file.
 *
 * @param header_list_pid If nonzero, the pid of the preprocessor for getting used headers.
 * Must be allowed to complete before we send the input file.
 *
 * @param local_cpu_lock_fd If != -1, file descriptor for the lock file.
 * Should be != -1 iff (host->cpp_where != DCC_CPP_ON_SERVER).
 * If != -1, the lock must be held on entry to this function,
 * and THIS FUNCTION WILL RELEASE THE LOCK.
 *
 * @param host Definition of host to send this job to.
 *
 * @param status on return contains the wait-status of the remote
 * compiler.
 *
 * Returns 0 on success, otherwise error.  Returning nonzero does not
 * necessarily imply the remote compiler itself succeeded, only that
 * there were no communications problems.
 *
 * TODO: consider refactoring this (perhaps as two separate subroutines?)
 * to avoid the need for releasing the lock as a side effect of this call.
 */
int dcc_compile_remote(char **argv,
                       char *input_fname,
                       char *cpp_fname,
                       char *header_list_fname,
                       char **files,
                       char *output_fname,
                       char *deps_fname,
                       char *server_stderr_fname,
                       pid_t cpp_pid,
                       pid_t header_list_pid,
                       int local_cpu_lock_fd,
                       struct dcc_hostdef *host,
                       int *status)
{
    int to_net_fd = -1, from_net_fd = -1;
    int ret;
    pid_t ssh_pid = 0;
    int ssh_status;
    off_t doti_size;
    struct timeval before, after;
    unsigned int n_files;

    if (gettimeofday(&before, NULL))
        rs_log_warning("gettimeofday failed");

    dcc_note_execution(host, argv);
    dcc_note_state(DCC_PHASE_CONNECT, input_fname, host->hostname, DCC_REMOTE);

    /* For ssh support, we need to allow for separate fds writing to and
     * reading from the network, because our connection to the ssh client may
     * be over pipes, which are one-way connections. */

    *status = 0;
    if ((ret = dcc_remote_connect(host, &to_net_fd, &from_net_fd, &ssh_pid)))
        goto out;

#ifdef HAVE_GSSAPI
    /* Perform requested security. */
    if(host->authenticate) {
        rs_log_info("Performing authentication.");

        if ((ret = dcc_gssapi_perform_requested_security(to_net_fd, from_net_fd)) != 0) {
            rs_log_crit("Failed to perform authentication.");
            goto out;
        }

        /* Context deleted here as we no longer need it.  However, we have it available */
        /* in case we want to use confidentiality/integrity type services in the future. */
        dcc_gssapi_delete_ctx(&distcc_ctx_handle);
    } else {
        rs_log_info("No authentication requested.");
    }
#endif

    dcc_note_state(DCC_PHASE_SEND, NULL, NULL, DCC_REMOTE);

    if (host->cpp_where == DCC_CPP_ON_SERVER) {
        if ((ret = dcc_send_header(to_net_fd, argv, host))) {
          goto out;
        }

        /* Here will sent just an empty string */
        if ((ret = try_exchange_precompiled_header(to_net_fd, from_net_fd, input_fname, status,
                                                   header_list_fname, header_list_pid))) {
            goto out;
        }

        n_files = dcc_argv_len(files);
        if ((ret = dcc_x_many_files(to_net_fd, n_files, files))) {
            goto out;
        }
    } else {
        /* This waits for cpp and puts its status in *status.  If cpp failed,
         * then the connection will have been dropped and we need not bother
         * trying to get any response from the server. */

        if ((ret = dcc_send_header(to_net_fd, argv, host)))
            goto out;

        if ((ret = try_exchange_precompiled_header(to_net_fd, from_net_fd, input_fname, status,
                                                   header_list_fname, header_list_pid))) {
            goto out;
        }

        if ((ret = dcc_wait_for_cpp(cpp_pid, status, input_fname)))
            goto out;

        /* We are done with local preprocessing.  Unlock to allow someone
         * else to start preprocessing. */
        if (local_cpu_lock_fd != -1) {
            dcc_unlock(local_cpu_lock_fd);
            local_cpu_lock_fd = -1;
        }

        if (*status != 0)
            goto out;

        if ((ret = dcc_x_file(to_net_fd, cpp_fname, "DOTI", host->compr,
                              &doti_size)))
            goto out;
    }

    rs_trace("client finished sending request to server");
    tcp_cork_sock(to_net_fd, 0);
    /* but it might not have been read in by the server yet; there's
     * 100kB or more of buffers in the two kernels. */

    /* OK, now all of the source has at least made it into the
     * client's TCP transmission queue, sometime soon the server will
     * start compiling it.  */
    dcc_note_state(DCC_PHASE_COMPILE, NULL, host->hostname, DCC_REMOTE);

    /* If cpp failed, just abandon the connection, without trying to
     * receive results. */
    if (ret == 0 && *status == 0) {
        ret = dcc_retrieve_results(from_net_fd, status, output_fname,
                                   deps_fname, server_stderr_fname, host);
    }

    if (gettimeofday(&after, NULL)) {
        rs_log_warning("gettimeofday failed");
    } else if (host->cpp_where == DCC_CPP_ON_CLIENT) {
        double secs, rate;

        dcc_calc_rate(doti_size, &before, &after, &secs, &rate);
        rs_log(RS_LOG_INFO|RS_LOG_NONAME,
               "%lu bytes from %s compiled on %s in %.4fs, rate %.0fkB/s",
               (unsigned long) doti_size, input_fname, host->hostname,
               secs, rate);
    }

  out:
    if (local_cpu_lock_fd != -1) {
        dcc_unlock(local_cpu_lock_fd);
        local_cpu_lock_fd = -1; /* Not really needed; just for consistency. */
    }

    /* Close socket so that the server can terminate, rather than
     * making it wait until we've finished our work. */
    if (to_net_fd != from_net_fd) {
        if (to_net_fd != -1)
            dcc_close(to_net_fd);
    }
    if (from_net_fd != -1)
        dcc_close(from_net_fd);

    /* Collect the SSH child.  Strictly this is unnecessary; it might slow the
     * client down a little when things could otherwise be proceeding in the
     * background.  But it helps make sure that we don't assume we succeeded
     * when something possibly went wrong, and it allows us to account for the
     * cost of the ssh child. */
    if (ssh_pid) {
        dcc_collect_child("ssh", ssh_pid, &ssh_status, timeout_null_fd); /* ignore failure */
    }

    return ret;
}
