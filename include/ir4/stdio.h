#ifndef _STDIO_H
#define _STDIO_H

#ifndef NULL
#define NULL ((void *)0)
#endif

extern int __c_putchar(int c);
#define putchar(c) __c_putchar(c)
extern int puts(const char *s);
extern int printf(const char *fmt, ...);

#endif
