module Vint.Util

import Data.Vect

public export
data NatCmp : Nat -> Nat -> Type where
    Less    : LT a b -> NatCmp a b
    Equal   : a = b  -> NatCmp a b
    Greater : GT a b -> NatCmp a b

export
compare : (a : Nat) -> (b : Nat) -> NatCmp a b
compare Z Z = Equal Refl
compare Z (S a) = Less $ LTESucc LTEZero
compare (S a) Z = Greater $ LTESucc LTEZero
compare (S a) (S b) = case compare a b of
    Less lt    => Less $ LTESucc lt
    Equal eq   => Equal $ cong eq
    Greater gt => Greater $ LTESucc gt


||| Helper: postulate that strCons increases length by one
strConsLen : (c : Char) -> (s : String) -> length (strCons c s) = 1 + length s
-- prim_lenString is primitive, so:
strConsLen c s = really_believe_me $ the (42 = 42) Refl


||| Split a string to a vector of characters of
||| the same size as the original string's length.
export
unpack' : (s : String) -> Vect (length s) Char
unpack' s with (strM s)
    unpack' ""             | StrNil = []
    unpack' (strCons c s') | (StrCons c s') =
        let
            cs = unpack' s'
            eq = strConsLen c s'
        in replace {P = \l => Vect l Char} (sym eq) (c :: cs)


||| Join a vector of characters into a string,
||| and prove it has the same length.
export
pack' : {len : Nat} -> Vect len Char -> (s : String ** length s = len)
pack' [] = ("" ** Refl)
pack' (c :: cs) =
    let
        (s' ** prf) = pack' cs
        eq = strConsLen c s'
        prf' = replace {P = \l => length (strCons c s') = 1 + l} prf eq
    in (strCons c s' ** prf')

export
minusPlus : (a : Nat) -> (b : Nat) -> {l : LTE b a} -> a - b + b = a
minusPlus Z Z = Refl
minusPlus a Z = replace {P = \c => c + 0 = a} (sym (minusZeroRight a)) (plusZeroRightNeutral a)
minusPlus Z (S b) impossible
minusPlus (S a) (S b) =
    let inductiveHypothesis = minusPlus a b
    in rewrite inductiveHypothesis in Refl
