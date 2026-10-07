/*
 * fanotify_shim.c — Lean @[extern] bridge to fanotify + io_uring
 *
 * One fd, recursive, entire mount. Zero CPU when idle.
 * The ring blocks on IORING_OP_READ of the fanotify fd.
 * On wake: batch statx, diff, invalidate.
 */
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <limits.h>
#include <linux/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/fanotify.h>
#include <sys/stat.h>
#include <unistd.h>

/* ── fanotify init ── */
LEAN_EXPORT lean_object* fanotify_init_watch(lean_object* root_path, lean_object* w) {
  (void)w;
#ifdef FAN_REPORT_DFID_NAME
  int fd = fanotify_init(FAN_CLASS_NOTIF | FAN_REPORT_DFID_NAME | FAN_NONBLOCK, O_RDONLY);
  if (fd < 0) {
    return lean_io_result_mk_error(
        lean_mk_io_user_error(lean_mk_string("fanotify_init failed (need CAP_SYS_FANOTIFY)")));
  }

  int rc = fanotify_mark(fd, FAN_MARK_ADD | FAN_MARK_FILESYSTEM,
                         FAN_CREATE | FAN_DELETE | FAN_MODIFY | FAN_MOVED_FROM | FAN_MOVED_TO |
                             FAN_ONDIR,
                         AT_FDCWD, lean_string_cstr(root_path));
  if (rc < 0) {
    close(fd);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("fanotify_mark failed")));
  }
  return lean_io_result_mk_ok(lean_box(fd));
#else
  (void)root_path;
  return lean_io_result_mk_error(
      lean_mk_io_user_error(lean_mk_string("fanotify not available (kernel too old)")));
#endif
}

/* ── read one batch of fanotify events ── */
LEAN_EXPORT lean_object* fanotify_read_events(uint32_t fd_val, lean_object* w) {
  (void)w;
  int fd = (int)fd_val;
  char buf[4096];
  ssize_t n = read(fd, buf, sizeof(buf));
  if (n < 0) {
    if (errno == EAGAIN || errno == EWOULDBLOCK) {
      return lean_io_result_mk_ok(lean_box(0)); /* no events ready */
    }
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("fanotify read failed")));
  }
  /* count events */
  uint32_t count = 0;
  struct fanotify_event_metadata* meta = (struct fanotify_event_metadata*)buf;
  while (FAN_EVENT_OK(meta, n)) {
    if (meta->fd >= 0) {
      close(meta->fd); /* close the event fd */
    }
    count++;
    meta = FAN_EVENT_NEXT(meta, n);
  }
  return lean_io_result_mk_ok(lean_box(count));
}

/* ── close fanotify fd ── */
LEAN_EXPORT lean_object* fanotify_close(uint32_t fd_val, lean_object* w) {
  (void)w;
  close((int)fd_val);
  return lean_io_result_mk_ok(lean_box(0));
}

/* ── batch statx: stat all files in a directory tree ── */
/* Returns a list of (path, mtime, size) as a Lean array */
static void walk_dir(const char* dir, lean_object** arr) {
  DIR* d = opendir(dir);
  if (!d) {
    return;
  }
  struct dirent* ent;
  while ((ent = readdir(d)) != NULL) {
    if (ent->d_name[0] == '.') {
      continue;
    }
    char path[PATH_MAX];
    snprintf(path, sizeof(path), "%s/%s", dir, ent->d_name);
    struct stat st;
    if (stat(path, &st) == 0) {
      /* push (path, mtime_sec, size) */
      lean_object* entry = lean_alloc_ctor(0, 3, 0);
      lean_ctor_set(entry, 0, lean_mk_string(path));
      lean_ctor_set(entry, 1, lean_box((size_t)st.st_mtime));
      lean_ctor_set(entry, 2, lean_box((size_t)st.st_size));
      *arr = lean_array_push(*arr, entry);
    }
    if (ent->d_type == DT_DIR) {
      walk_dir(path, arr);
    }
  }
  closedir(d);
}

LEAN_EXPORT lean_object* fanotify_scan_tree(lean_object* root_path, lean_object* w) {
  (void)w;
  lean_object* arr = lean_mk_empty_array();
  walk_dir(lean_string_cstr(root_path), &arr);
  return lean_io_result_mk_ok(arr);
}
