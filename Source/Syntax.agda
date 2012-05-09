module Source.Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.List
open import Data.Product

-- base types
data Type : Set where
  Un : Type
  Bo : Type
  In : Type
  AR : Type

GroupID : ℕ → Set
GroupID n = Fin n

TaskID : ℕ → Set
TaskID n = Fin n

-- actor references: identifies the group and the task
data ARef (n m : ℕ) : Set where
  AR : GroupID n → TaskID m → ARef n m

-- constant context :)
CCtx : Set
CCtx = List Type

-- variable context: maps variables to their types
Ctx : Set
Ctx = List Type

-- function contxt: maps functions to parameter types and return type
FCtx : Set
FCtx = List (Ctx × Type)

data Val : Type → Set where
    U : Val Un
    A : (n m : ℕ) → ARef n m → Val AR
    N : ℕ → Val In
    B : Bool → Val Bo

data Const : CCtx → Type → Set where
    z : ∀{Ξ} → (ξ : Type) → Const (ξ ∷ Ξ) ξ
    s : ∀{Ξ ξ σ} → Const Ξ ξ → Const (σ ∷ Ξ) ξ

data Var : Ctx → Type → Set where
    z : ∀{Γ} → (τ : Type) → Var (τ ∷ Γ) τ
    s : ∀{τ σ Γ} → Var Γ τ → Var (σ ∷ Γ) τ

data Fun : FCtx → Ctx → Type → Set where
    z : ∀{Δ} → (Γ : Ctx) → (τ : Type) → Fun ((Γ , τ) ∷ Δ) Γ τ
    s : ∀{Γ Δ Λ σ τ} → Fun Δ Γ τ → Fun ((Λ , σ) ∷ Δ) Γ τ

data Exp (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) : Type → Set

-- list of expressions
data ExpList (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) : Ctx → Set where
    [] : ExpList Δ Γ Ξ []
    _∷_ : ∀{τ T} → Exp Δ Γ Ξ τ → ExpList Δ Γ Ξ T → ExpList Δ Γ Ξ (τ ∷ T)

data Exp (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) where
    var   : ∀{τ} → Var Γ τ → Exp Δ Γ Ξ τ
    val   : ∀{τ} → Val τ → Exp Δ Γ Ξ τ
    const : ∀{τ} → Const Ξ τ → Exp Δ Γ Ξ τ
    _≐_   : ∀{τ} → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ Bo
    ¬_    : Exp Δ Γ Ξ Bo → Exp Δ Γ Ξ Bo
    _∔_   : Exp Δ Γ Ξ In → Exp Δ Γ Ξ In → Exp Δ Γ Ξ In
    _⊻_   : Exp Δ Γ Ξ Bo → Exp Δ Γ Ξ Bo → Exp Δ Γ Ξ Bo
    avail : Exp Δ Γ Ξ Bo
    _（_） : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Ξ Λ → Exp Δ Γ Ξ τ
    spawn : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Ξ Λ → Exp Δ Γ Ξ AR
    spawng : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Ξ Λ → Exp Δ Γ Ξ AR
    yield : Exp Δ Γ Ξ Un

-- former statements
    _≔_           : ∀{τ} → Var Γ τ → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ Un
    skip          : Exp Δ Γ Ξ Un
    _,_           : ∀{τ} → Exp Δ Γ Ξ Un → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ τ
    If_then_else_ : ∀{τ} → Exp Δ Γ Ξ Bo → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ τ
    While_do_     : Exp Δ Γ Ξ Bo → Exp Δ Γ Ξ Un → Exp Δ Γ Ξ Un -- TODO generalize it to τ, not just unit
    send          : ∀{τ} → Exp Δ Γ Ξ AR → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ τ
-- TODO substitution of received messages
    receive       : ∀{τ} → Exp Δ Γ (Un ∷ Ξ) τ → Exp Δ Γ (AR ∷ Ξ) τ → Exp Δ Γ (In ∷ Ξ) τ → Exp Δ Γ (Bo ∷ Ξ) τ → Exp Δ Γ Ξ τ
    ignore        : ∀{τ} → Exp Δ Γ Ξ τ → Exp Δ Γ Ξ Un
    Let           : ∀{τ ξ} → Exp Δ Γ Ξ ξ → Exp Δ Γ (ξ ∷ Ξ) τ → Exp Δ Γ Ξ τ

data _values {Γ Δ Ξ} : ∀{Λ} → ExpList Γ Δ Ξ Λ → Set where
    []-values : [] values
    ∷-values  : ∀{τ T} → (v : Val τ) → (l : ExpList Γ Δ Ξ T) → l values → ((val v) ∷ l) values

data State : Ctx → Set where
  []  : State []
  _∷_ : ∀{γ Γ} → Val γ → State Γ → State (γ ∷ Γ)

lkp : ∀{τ Γ} → State Γ → (x : Var Γ τ) → Val τ
lkp []       ()
lkp (x ∷ _)  (z _) = x
lkp (_ ∷ st) (s x) = lkp st x

upd : ∀{τ Γ} → Var Γ τ → Val τ → State Γ → State Γ
upd ()    _  []
upd (z _) va (_ ∷ st) = va ∷ st
upd (s x) va (v ∷ st) = v ∷ upd x va st

-- append messages to the end (_∷ʳ_), pop them from the head (_∷_)
Queue : Set
Queue = List (∃ λ τ → Val τ)