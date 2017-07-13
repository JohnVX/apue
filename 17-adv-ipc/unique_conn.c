#include "apue.h"

int serv_listen(const char *name);

int serv_accept(int listenfd, uid_t *uidptr);

int cli_conn(const char *name);

