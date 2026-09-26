#ifndef _SYS_IOCTL_H
#define _SYS_IOCTL_H
#include <bits/features.h>

#define TCGETS 0x5401
#define TCSETS 0x5402
#define TCSETSW 0x5403
#define TCSETSF 0x5404
#define TIOCGWINSZ 0x5413
#define TIOCSWINSZ 0x5414
#define TIOCGPGRP 0x540F
#define TIOCSPGRP 0x5410
#define FIONREAD 0x541B
#define FIONBIO 0x5421
#define FIOCLEX 0x5451
#define FIONCLEX 0x5450
#define TIOCNOTTY 0x5422
#define TIOCSCTTY 0x540E

struct winsize {
    unsigned short ws_row, ws_col, ws_xpixel, ws_ypixel;
};

__BEGIN_DECLS
int ioctl(int, unsigned long, ...);
__END_DECLS

#endif
