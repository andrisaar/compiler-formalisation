module Util.Vector where

open import Data.Maybe
open import Data.Fin hiding (_≤_; _<_)
open import Data.Nat
open import Data.Product hiding (map)

infixr 5 _∷_ _++_
data Vec (A : Set)(n : ℕ) : ℕ → Set where
  [] : Vec A n n
  _∷_ : ∀{m} → A → Vec A n m →  Vec A n (suc m)

_++_ : ∀{l n m}{A : Set} → Vec A n m → Vec A l n → Vec A l m
[] ++ r = r
(x ∷ l) ++ r = x ∷ l ++ r

_∷ʳ_ : ∀{n m}{A : Set} → Vec A (suc n) m → A → Vec A n m
[] ∷ʳ e = e ∷ []
(x ∷ vec) ∷ʳ e = x ∷ (vec ∷ʳ e)

[_] : ∀{A : Set}{n} → A → Vec A n (suc n)
[ x ] = x ∷ []

map : ∀{n m}{A B : Set} → (f : A → B) → Vec A n m → Vec B n m 
map f [] = []
map f (x ∷ vec) = f x ∷ map f vec

lastidx : ∀{n}{A : Set} → Vec A zero (suc n) → Fin (suc n)
lastidx (_ ∷ []) = zero
lastidx (_ ∷ (x ∷ vec)) = suc (lastidx (x ∷ vec))

{-
lookup : ∀{n}{A : Set} → Fin n → Vec A zero n → A
lookup () []
lookup zero      (x ∷ vec) = x
lookup (suc idx) (x ∷ vec) = lookup idx vec

lookup₂ : ∀{m n}{A : Set} → Fin n → Vec A zero m → A → Vec A (suc m) n → A
lookup₂ zero vec₁ x [] = x
lookup₂ zero vec₁ x (x₁ ∷ vec₂) = x₁
lookup₂ (suc idx) vec₁ x [] = lookup idx vec₁
lookup₂ (suc idx) vec₁ x (x₁ ∷ vec₂) = lookup₂ idx vec₁ x vec₂

_[_]≔_ : ∀{m}{A : Set} → Vec A zero m → Fin m → A → Vec A zero m
[] [ () ]≔ val
(x ∷ vec) [ zero ]≔ val = val ∷ vec
(x ∷ vec) [ suc idx ]≔ val = x ∷ (vec [ idx ]≔ val)

_&_[_]≔_ : ∀{m n}{A : Set} → Vec A zero n → Vec A n m → Fin m → A → Vec A zero n × Vec A n m
vec₁ & [] [ idx ]≔ val = vec₁ [ idx ]≔ val , []
vec₁ & x ∷ vec₂ [ zero ]≔ val = vec₁ , val ∷ vec₂
vec₁ & x ∷ vec₂ [ suc idx ]≔ val with vec₁ & vec₂ [ idx ]≔ val
... | vec₁' , vec₂' = vec₁' , x ∷ vec₂'

_&_&_[_]≔_ : ∀{m n}{A : Set} → Vec A zero m → A → Vec A (suc m) n → Fin n → A → Vec A zero m × A × Vec A (suc m) n
vec₁ & _ & [] [ zero ]≔ val = vec₁ , val , []
vec₁ & x & [] [ suc idx ]≔ val = vec₁ [ idx ]≔ val , x , []
vec₁ & x & _ ∷ vec₂ [ zero ]≔ val = vec₁ , x , val ∷ vec₂
vec₁ & x & y ∷ vec₂ [ suc idx ]≔ val with vec₁ & x & vec₂ [ idx ]≔ val
... | vec₁' , x' , vec₂' = vec₁' , x' , y ∷ vec₂'

-}

down : (n : ℕ) → Fin (suc n) → Maybe (Fin n)
down zero    zero    = nothing
down zero    (suc ())
down (suc x) zero    = just zero
down (suc x) (suc y) with down x y
... | nothing = nothing
... | just z = just (suc z)

lookup : ∀{n}{A : Set} → Fin n → Vec A zero n → A
lookup () []
lookup idx (x ∷ vec) with down _ idx
... | nothing = x
... | just z = lookup z vec

lookup₂ : ∀{m n}{A : Set} → Fin n → Vec A zero m → A → Vec A (suc m) n → A
lookup₂ idx vec₁ x [] with down _ idx 
... | nothing = x
... | just z = lookup z vec₁
lookup₂ idx vec₁ x (y ∷ vec₂) with down _ idx
... | nothing = y
... | just z = lookup₂ z vec₁ x vec₂

_[_]≔_ : ∀{m}{A : Set} → Vec A zero m → Fin m → A → Vec A zero m
[] [ () ]≔ val
(x ∷ vec) [ idx ]≔ val with down _ idx
... | nothing = val ∷ vec 
... | just z = x ∷ (vec [ z ]≔ val)

open import Relation.Binary.PropositionalEquality renaming ([_] to ⟦_⟧)

down-inject : ∀{n} → (m : Fin n) → down n (inject₁ m) ≡ just m
down-inject zero = refl
down-inject (suc m) rewrite down-inject m = refl

lookup-extend : ∀{A : Set}{x y : A}{n}{vec : Vec A zero n} → (m : Fin n) → lookup m vec ≡ x → lookup (inject₁ m) (y ∷ vec) ≡ x
lookup-extend zero    p = p
lookup-extend (suc m) p rewrite down-inject m = p

down-lastidx : ∀{n}{A : Set}{x : A} → (vec : Vec A zero n) → down n (lastidx (x ∷ vec)) ≡ nothing
down-lastidx [] = refl
down-lastidx (x ∷ vec) rewrite down-lastidx {x = x} vec = refl

lookup-lastidx : ∀{n}{A : Set}{x : A} → (vec : Vec A zero n) → lookup (lastidx (x ∷ vec)) (x ∷ vec) ≡ x
lookup-lastidx [] = refl
lookup-lastidx (x ∷ vec) rewrite down-lastidx {x = x} vec = refl

down-zero : (m : Fin 1) → down zero m ≡ nothing
down-zero m with down 0 m
... | nothing = refl
... | just ()

lookup-suc-eq : ∀{n} → (idx : Fin n) → (vec : Vec ℕ zero n) → suc (lookup idx vec) ≡ lookup idx (vec [ idx ]≔ suc (lookup idx vec))
lookup-suc-eq () []
lookup-suc-eq {suc zero} idx (x ∷ []) rewrite down-zero idx | down-zero idx = refl
lookup-suc-eq {suc (suc n)} idx (x ∷ vec) with down (suc n) idx | inspect (down (suc n)) idx
... | just x' | ⟦ eq ⟧ rewrite eq = lookup-suc-eq x' vec
... | nothing | ⟦ eq ⟧ rewrite eq = refl


empty-concatl : ∀{m n}{A : Set} → (xs : Vec A m n) → [] ++ xs ≡ xs
empty-concatl [] = refl
empty-concatl (x ∷ xs) = cong (λ s → x ∷ s) (empty-concatl xs)

empty-concatr : ∀{m n}{A : Set} → (xs : Vec A m n) → xs ++ [] ≡ xs
empty-concatr [] = refl
empty-concatr (x ∷ xs) = cong (λ s → x ∷ s) (empty-concatr xs)

append-concat : ∀{l m n}{A : Set}{x : A} → (xs : Vec A l m) → (ys : Vec A (suc m) n) → ys ++ (x ∷ xs) ≡ ys ∷ʳ x ++ xs
append-concat xs [] = refl
append-concat {x = x} xs (x₂ ∷ ys) = cong (λ s → x₂ ∷ s) (append-concat {x = x} xs ys)

snoc-concat : ∀{n m}{x} → (S : Vec ℕ (suc n) m) → (T : Vec ℕ zero n) → S ∷ʳ x ++ T ≡ S ++ x ∷ T
snoc-concat [] T = refl
snoc-concat (x ∷ S) T = cong (λ S → x ∷ S) (snoc-concat S T)

_&_[_]≔_ : ∀{m n}{A : Set} → Vec A zero n → Vec A n m → Fin m → A  → Vec A zero n × Vec A n m
vec₁ & [] [ idx ]≔ val = vec₁ [ idx ]≔ val , []
vec₁ & x ∷ vec₂ [ idx ]≔ val with down _ idx
... | nothing = vec₁ , val ∷ vec₂
... | just z with vec₁ & vec₂ [ z ]≔ val
...    | vec₁' , vec₂' = vec₁' , x ∷ vec₂'

_&_&_[_]≔_ : ∀{m n}{A : Set} → Vec A zero m → A → Vec A (suc m) n → Fin n → A → Vec A zero m × A × Vec A (suc m) n
vec₁ & x & [] [ idx ]≔ val with down _ idx
... | just z = vec₁ [ z ]≔ val , x , []
... | nothing = vec₁ , val , []
vec₁ & x & y ∷ vec₂ [ idx ]≔ val with down _ idx
... | nothing = vec₁ , x , val ∷ vec₂
... | just z with vec₁ & x & vec₂ [ z ]≔ val 
...      | vec₁' , x' , vec₂' = vec₁' , x' , y ∷ vec₂'
