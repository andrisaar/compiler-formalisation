module Target.Syntax where

open import Data.Product
open import Data.List
open import Data.Vec

data Type : Set where
  
data Flag : Set where
  ○ : Flag
  ● : Type → Type → Flag -- @cps[B, C] of Scala
{-
_◎_ : Flag → Flag → Flag
○ ◎ ○ = ○
● B C ◎ _ = ● B C
○ ◎ ● B C = ● B C
-}

Ctx : Set
Ctx = List Type

FCtx : Set
FCtx = List (Ctx × Type × Flag)

data Var : Ctx → Type → Set where
  z : ∀{Γ} → (τ : Type) → Var (τ ∷ Γ) τ
  s : ∀{Γ σ τ} → Var Γ τ → Var (σ ∷ Γ) τ

data Fun : FCtx → Ctx → Type → Flag → Set where
  z : ∀{Δ Γ τ f} → Fun ((Γ , τ , f) ∷ Δ) Γ τ f
  s : ∀{Γ Δ Λ τ f σ g} → Fun Δ Γ τ f → Fun ((Λ , σ , g) ∷ Δ) Γ τ f

data Exp  (Δ : FCtx) (Γ : Ctx) : Type → Flag → Set

data ExpList (Δ : FCtx) (Γ : Ctx) : Ctx → Set where
  [] : ExpList Δ Γ []
  _∷_ : ∀{σ Σ} → Exp Δ Γ σ {!!} → ExpList Δ Γ (σ ∷ Σ)

data Exp (Δ : FCtx) (Γ : Ctx) where
  reset : ∀{B C} → Exp Δ Γ B (● B C) → Exp Δ Γ C ○
  shift : ∀{A B C} → Exp ((Data.List.[ A ] , B , ○) ∷ Δ) Γ C ○ → Exp Δ Γ A (● B C)
  var   : ∀{τ f} → Var Γ τ → Exp Δ Γ τ f
  _（_） : ∀{Λ τ f} → Fun Δ Λ τ f → ExpList Δ Γ Λ → Exp Δ Γ τ f
  
  
