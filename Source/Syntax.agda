module Source.Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.List
open import Data.Product
--open import Data.Vec

open import Util.Vector

-- base types
data Type : Set where
  Un : Type
  Bo : Type
  In : Type
  AR : Type

-- task context
TCtx : Set
TCtx = ∃ λ mgid → Vec ℕ zero mgid

{-
GroupID : TCtx → Set
GroupID T = Fin (proj₁ T)
-}

TaskID : (T : TCtx) → Fin (proj₁ T) → Set
TaskID T n = Fin (lookup n (proj₂ T))

-- actor references: identifies the group and the task
--data ARef : TCtx → Set where
--  AR : ∀{T} → (gid : GroupID (proj₁ T)) → TaskID (lookup gid (proj₂ T)) → ARef T

-- constant context :)
CCtx : Set
CCtx = List Type

-- variable context: maps variables to their types
Ctx : Set
Ctx = List Type

-- function contxt: maps functions to parameter types and return type
FCtx : Set
FCtx = List (Ctx × Type)

data Val (T : TCtx) : Type → Set where
    U : Val T Un
    A : ∀{n} → TaskID T n → Val T AR
    N : ℕ → Val T In
    B : Bool → Val T Bo

data Const : CCtx → Type → Set where
    z : ∀{Ξ} → (ξ : Type) → Const (ξ ∷ Ξ) ξ
    s : ∀{Ξ ξ σ} → Const Ξ ξ → Const (σ ∷ Ξ) ξ

data Var : Ctx → Type → Set where
    z : ∀{Γ} → (τ : Type) → Var (τ ∷ Γ) τ
    s : ∀{τ σ Γ} → Var Γ τ → Var (σ ∷ Γ) τ

data Fun : FCtx → Ctx → Type → Set where
    z : ∀{Δ} → (Γ : Ctx) → (τ : Type) → Fun ((Γ , τ) ∷ Δ) Γ τ
    s : ∀{Γ Δ Λ σ τ} → Fun Δ Γ τ → Fun ((Λ , σ) ∷ Δ) Γ τ

data Exp (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) (T : TCtx) : Type → Set

-- list of expressions
data ExpList (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) (T : TCtx) : Ctx → Set where
    [] : ExpList Δ Γ Ξ T []
    _∷_ : ∀{σ Σ} → Exp Δ Γ Ξ T σ → ExpList Δ Γ Ξ T Σ → ExpList Δ Γ Ξ T (σ ∷ Σ)

data Exp (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) (T : TCtx) where
    var   : ∀{τ} → Var Γ τ → Exp Δ Γ Ξ T τ
    val   : ∀{τ} → Val T τ → Exp Δ Γ Ξ T τ
    const : ∀{τ} → Const Ξ τ → Exp Δ Γ Ξ T τ
    _≐_   : ∀{τ} → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T Bo
    ¬_    : Exp Δ Γ Ξ T Bo → Exp Δ Γ Ξ T Bo
    _∔_   : Exp Δ Γ Ξ T In → Exp Δ Γ Ξ T In → Exp Δ Γ Ξ T In
    _⊻_   : Exp Δ Γ Ξ T Bo → Exp Δ Γ Ξ T Bo → Exp Δ Γ Ξ T Bo
    avail : Exp Δ Γ Ξ T Bo
    _（_） : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Ξ T Λ → Exp Δ Γ Ξ T τ
    spawn : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Ξ T Λ → Exp Δ Γ Ξ T AR
    spawng : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Ξ T Λ → Exp Δ Γ Ξ T AR
    yield : Exp Δ Γ Ξ T Un

-- former statements
    _≔_           : ∀{τ} → Var Γ τ → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T Un
    skip          : Exp Δ Γ Ξ T Un
    _,_           : ∀{τ} → Exp Δ Γ Ξ T Un → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T τ
    If_then_else_ : ∀{τ} → Exp Δ Γ Ξ T Bo → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T τ
    While_do_     : Exp Δ Γ Ξ T Bo → Exp Δ Γ Ξ T Un → Exp Δ Γ Ξ T Un -- TODO generalize it to τ, not just unit
    send          : ∀{τ} → Exp Δ Γ Ξ T AR → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T τ
    receive       : ∀{τ} → Exp Δ Γ (Un ∷ Ξ) T τ → Exp Δ Γ (AR ∷ Ξ) T τ → Exp Δ Γ (In ∷ Ξ) T τ → Exp Δ Γ (Bo ∷ Ξ) T τ → Exp Δ Γ Ξ T τ
    ignore        : ∀{τ} → Exp Δ Γ Ξ T τ → Exp Δ Γ Ξ T Un
    Let           : ∀{τ ξ} → Exp Δ Γ Ξ T ξ → Exp Δ Γ (ξ ∷ Ξ) T τ → Exp Δ Γ Ξ T τ

data _values {Γ Δ Ξ T} : ∀{Λ} → ExpList Γ Δ Ξ T Λ → Set where
    []-values : [] values
    ∷-values  : ∀{σ Σ} → (v : Val T σ) → (l : ExpList Γ Δ Ξ T Σ) → l values → ((val v) ∷ l) values

data State (T : TCtx) : Ctx → Set where
  []  : State T []
  _∷_ : ∀{γ Γ} → Val T γ → State T Γ → State T (γ ∷ Γ)

lkp : ∀{τ Γ T} → State T Γ → (x : Var Γ τ) → Val T τ
lkp []       ()
lkp (x ∷ _)  (z _) = x
lkp (_ ∷ st) (s x) = lkp st x

upd : ∀{τ Γ T} → Var Γ τ → Val T τ → State T Γ → State T Γ
upd ()    _  []
upd (z _) va (_ ∷ st) = va ∷ st
upd (s x) va (v ∷ st) = v ∷ upd x va st

-- append messages to the end (_∷ʳ_), pop them from the head (_∷_)
Queue : TCtx → Set
Queue T = List (∃ λ τ → Val T τ)

