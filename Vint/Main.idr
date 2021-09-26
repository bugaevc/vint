module Main

import Vint.Curses
import Vint.Buffer

%include C "sys/signal.h"

rand : IO Int
rand = foreign FFI_C "rand" (IO Int)

mutual
    handleSignal : Int -> IO ()
    handleSignal signo = do
        printw ("Got signal " ++ show signo ++ "\n")
        setupSignalHandler

    SIGINT : IO Int
    SIGINT = foreign FFI_C "#SIGINT" (IO Int)

    SignalHandler : Type
    SignalHandler = CFnPtr (Int -> ())

    rawHandler : Int -> ()
    rawHandler = unsafePerformIO . handleSignal

    setupSignalHandler : IO ()
    setupSignalHandler = do
        foreign FFI_C "signal" (Int -> SignalHandler -> IO ()) !SIGINT (MkCFnPtr rawHandler)
        pure ()

whileTrue : IO () -> IO ()
whileTrue f = do
    f
    whileTrue f

main : IO ()
main = do
    setupSignalHandler
    initscr
    raw
    noecho
    let buffer = MkBuffer ["Hello", "World"] Center 0
    displayBuffer buffer 10
    refresh
    whileTrue $ do
        printw ("Got back " ++ show !getch ++ "\n")
        printw ("A random value is " ++ show !rand ++ "\n")
        refresh
    getch
    endwin
    pure ()
