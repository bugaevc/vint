#include <ncurses.h>

#undef getstr
#define getstr idris_getstr

static inline int getCOLS() { return COLS; }
static inline int getLINES() { return LINES; }
