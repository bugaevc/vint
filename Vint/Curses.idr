module Vint.Curses

%lib C "ncurses"
%include C "mycurses.h"
%access export

initscr : IO Ptr
initscr = foreign FFI_C "initscr" (IO Ptr)

endwin : IO Int
endwin = foreign FFI_C "endwin" (IO Int)

refresh : IO ()
refresh = foreign FFI_C "refresh" (IO ())

-- FIXME: varargs?
printw : String -> IO Int
printw = foreign FFI_C "printw" (String -> IO Int)

getch : IO Int
getch = foreign FFI_C "getch" (IO Int)

raw : IO Int
raw = foreign FFI_C "raw" (IO Int)

echo : IO Int
echo = foreign FFI_C "echo" (IO Int)

noecho : IO Int
noecho = foreign FFI_C "noecho" (IO Int)

move : Int -> Int -> IO Int
move = foreign FFI_C "move" (Int -> Int -> IO Int)

clrtoeol : IO Int
clrtoeol = foreign FFI_C "clrtoeol" (IO Int)

COLS : IO Int
COLS = foreign FFI_C "getCOLS" (IO Int)

LINES : IO Int
LINES = foreign FFI_C "getLINES" (IO Int)
