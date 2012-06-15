module Util.Eq where

open import Data.Bool
open import Data.Nat

_≡b_ : Bool → Bool → Bool
true  ≡b true  = true
false ≡b false = true
_     ≡b _     = false

_≡n_ : ℕ → ℕ → Bool
zero    ≡n zero    = true
zero    ≡n (suc _) = false
(suc _) ≡n zero    = false
(suc a) ≡n (suc b) = a ≡n b
