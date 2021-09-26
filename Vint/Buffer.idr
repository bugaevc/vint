module Vint.Buffer

import Data.Vect

import Vint.Curses
import Vint.Util

%default total

public export
data Alignment : Type where
    Left : Alignment
    Center : Alignment
    Right: Alignment
    Justify: Alignment

public export
record Buffer where
    constructor MkBuffer
    lines : List String
    alignment : Alignment
    firstVisibleLine : Nat
    -- firstVisibleLineIsInBounds : InBounds firstVisibleLine lines

padLine : (line : String) -> Alignment -> (width : Nat) -> {l : LTE (length line) width} -> String
padLine line alignment width =
    let extra = width - (length line); padding = pack $ replicate extra ' ' in
    case alignment of
        Left => line ++ padding
        Center => ""
        Right => padding ++ line
        Justify => ""


trimLine :
    Alignment ->
    (width : Nat) ->
    (line : String) ->
    {l : LTE width (length line)} ->
    (s : String ** length s = width)

trimLine alignment width line =
    let
        unpacked = unpack' line
        l : LTE width (length line) = _
        dropped = doDrop (length line) width unpacked {l2 = l}
    in
        pack' dropped
    where
        doDrop :
            (len : Nat) ->
            (width : Nat) ->
            (chars : Vect len Char) ->
            { l2 : LTE width len  } ->
            Vect width Char
        doDrop len width chars = case alignment of
            Right => drop (len - width) chars
    


alignLine : String -> Alignment -> Nat -> String
alignLine line Right availableWidth =
    case compare availableWidth (length line) of
        Less lt => let lte = lteSuccLeft lt in
            (pack . drop (length line - availableWidth) . unpack) line
        Equal => line
        Greater gt => padLine line Right availableWidth { l = lteSuccLeft gt }



displayLine : Buffer -> Nat -> IO ()
displayLine buffer lineNo = do
    let vLineNo = lineNo + firstVisibleLine buffer
    let lns = lines buffer
    move (cast lineNo) 0
    case inBounds vLineNo lns of
        Yes _ => ignore (printw $ index vLineNo lns)
        No _ => pure ()
    clrtoeol
    pure ()

export
displayBuffer : Buffer -> Nat -> IO ()
displayBuffer buffer availableLines = do
    _ <- for [0..availableLines] $ displayLine buffer
    pure ()
