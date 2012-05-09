module Source.EvalCtx where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (group)
open import Data.List
open import Data.Maybe
open import Data.Product

open import Source.Syntax

-- evaluation ctx, indexed by the type of the hole and the return type
data E (Δ : FCtx)(Γ : Ctx)(Ξ : CCtx) : Type → Type → Set

data FunE (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) : Ctx → Set where
    empty : FunE Δ Γ Ξ []
    val : ∀{φ Φ} → Val φ → FunE Δ Γ Ξ Φ → FunE Δ Γ Ξ (φ ∷ Φ)
    exp : ∀{τ φ Φ} → E Δ Γ Ξ τ φ → ExpList Δ Γ Ξ Φ → FunE Δ Γ Ξ (φ ∷ Φ)

-- Eval ctx : variable context, var ctx that goes in the hole, function context, type expected in the hole, return type
data E (Δ : FCtx)(Γ : Ctx)(Ξ : CCtx) where
    □  : ∀{τ} → E Δ Γ Ξ τ τ
    ¬-E : ∀{τ} → E Δ Γ Ξ τ Bo → E Δ Γ Ξ τ Bo                              -- ¬ E
    ∨l-E : ∀{τ} → E Δ Γ Ξ τ Bo → Exp Δ Γ Ξ Bo → E Δ Γ Ξ τ Bo                 -- E ∨ e  
    ∨r-E : ∀{τ} → Val Bo → E Δ Γ Ξ τ Bo → E Δ Γ Ξ τ Bo -- v ∨ E            -- what about true ∨ E ?
    =l-E : ∀{A B} → E Δ Γ Ξ A B → Exp Δ Γ Ξ B → E Δ Γ Ξ A Bo                 -- E = e
    =r-E : ∀{A B} → Val B → E Δ Γ Ξ A B → E Δ Γ Ξ A Bo -- v = E
    +l-E : ∀{A} → E Δ Γ Ξ A In → Exp Δ Γ Ξ In → E Δ Γ Ξ A In                 -- E + e  
    +r-E : ∀{A} → Val In → E Δ Γ Ξ A In → E Δ Γ Ξ A In -- v + E
    
    call-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Ξ Λ → E Δ Γ Ξ A τ
    spawn-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Ξ Λ → E Δ Γ Ξ A AR
    spawng-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Ξ Λ → E Δ Γ Ξ A AR

    ≔-E : ∀{A τ} → (v : Var Γ τ) → E Δ Γ Ξ A τ → E Δ Γ Ξ A Un      -- x ≔ E
    ,-E : ∀{A B} → E Δ Γ Ξ A Un → Exp Δ Γ Ξ B → E Δ Γ Ξ A B                 -- E , e
    if-E : ∀{A B} → E Δ Γ Ξ A Bo → Exp Δ Γ Ξ B → Exp Δ Γ Ξ B → E Δ Γ Ξ A B     -- If E then e else e
    ignore-E : ∀{A B} → E Δ Γ Ξ A B → E Δ Γ Ξ A Un -- ignore E
    sendl-E : ∀{A B} → E Δ Γ Ξ A AR → Exp Δ Γ Ξ B → E Δ Γ Ξ A B                 -- send E e
    sendr-E : ∀{A B} → Val AR → E Δ Γ Ξ A B → E Δ Γ Ξ A B -- send v E
    Let-E : ∀{A σ τ} → E Δ Γ Ξ A σ → Exp Δ Γ (σ ∷ Ξ) τ → E Δ Γ Ξ A τ -- let E e

infix 4 _≡_[_]
infix 4 _≡′_[_]

data _≡_[_] {Γ Δ Ξ} : ∀{τ φ} → Exp Δ Γ Ξ τ → E Δ Γ Ξ φ τ → Exp Δ Γ Ξ φ → Set

data _≡′_[_] {Γ Δ Ξ} : ∀{φ ctx} → ExpList Δ Γ Ξ ctx → FunE Δ Γ Ξ ctx → Exp Δ Γ Ξ φ → Set where
    exp-≡′ : ∀{ctx φ}{e' : Exp Δ Γ Ξ φ}{τ}{E : E Δ Γ Ξ φ τ}{e}{l : ExpList Δ Γ Ξ ctx} → 
         e ≡ E [ e' ] → 
         e ∷ l ≡′ exp E l [ e' ]
    val-≡′ : ∀{ctx l}{E : FunE Δ Γ Ξ ctx}{τ}{υ : Val τ}{φ}{e : Exp Δ Γ Ξ φ} → 
         l ≡′ E [ e ] → 
         (val υ) ∷ l ≡′ val υ E [ e ]

data _≡_[_] {Γ Δ Ξ} where
    exp-≡ : ∀{τ} {e : Exp Δ Γ Ξ τ} → -- e redex →
      e ≡ □ [ e ]
    =l-≡ : ∀{τ φ E} {e₀ e₁ : Exp Δ Γ Ξ τ} {e : Exp Δ Γ Ξ φ} → e₀ ≡ E [ e ] → 
      e₀ ≐ e₁ ≡ =l-E E e₁ [ e ]
    =r-≡ : ∀{A B E} {e₀ : Val A} {e₁ : Exp Δ Γ Ξ A} {e : Exp Δ Γ Ξ B} → e₁ ≡ E [ e ] → 
      val e₀ ≐ e₁ ≡ =r-E e₀ E [ e ]
    ¬-≡ : ∀{B E} {e₀ : Exp Δ Γ Ξ Bo}{e : Exp Δ Γ Ξ B} → e₀ ≡ E [ e ] → 
      ¬ e₀ ≡ ¬-E E [ e ]
    +l-≡ : ∀{B E} {e₀ e₁ : Exp Δ Γ Ξ In} {e : Exp Δ Γ Ξ B} → e₀ ≡ E [ e ] → 
      e₀ ∔ e₁ ≡ +l-E E e₁ [ e ]
    +r-≡ : ∀{B E} {e₀ : Val In} {e₁ : Exp Δ Γ Ξ In} {e : Exp Δ Γ Ξ B} → e₁ ≡ E [ e ] → 
      val e₀ ∔ e₁ ≡ +r-E e₀ E [ e ]
    ∨l-≡ : ∀{B E} {e₀ e₁ : Exp Δ Γ Ξ Bo} {e : Exp Δ Γ Ξ B} → e₀ ≡ E [ e ] → 
      e₀ ⊻ e₁ ≡ ∨l-E E e₁ [ e ]
    ∨r-≡ : ∀{B E} {e₀ : Val Bo} {e₁ : Exp Δ Γ Ξ Bo} {e : Exp Δ Γ Ξ B} → e₁ ≡ E [ e ] → 
      val e₀ ⊻ e₁ ≡ ∨r-E e₀ E [ e ]
    ≔-≡ : ∀{τ φ} {x : Var Γ φ} {e₀ : Exp Δ Γ Ξ φ}{e : Exp Δ Γ Ξ τ} {E : E Δ Γ Ξ τ φ} → e₀ ≡ E [ e ] → 
      x ≔ e₀ ≡ ≔-E x E [ e ]
    if-≡ : ∀{A B E e₀} {e₁ e₂ : Exp Δ Γ Ξ A} {e : Exp Δ Γ Ξ B} → e₀ ≡ E [ e ] → 
      If e₀ then e₁ else e₂ ≡ if-E E e₁ e₂ [ e ]
    ignore-≡ : ∀{A B E} {e₀ : Exp Δ Γ Ξ A}{e : Exp Δ Γ Ξ B} → e₀ ≡ E [ e ] → 
      ignore e₀ ≡ ignore-E E [ e ]
    sendl-≡ : ∀{A B E e₁} {e₂ : Exp Δ Γ Ξ B}{e : Exp Δ Γ Ξ A} → e₁ ≡ E [ e ] →
      send e₁ e₂ ≡ sendl-E E e₂ [ e ]
    sendr-≡ : ∀{A B E v₁} {e₂ : Exp Δ Γ Ξ B} {e : Exp Δ Γ Ξ A} → e₂ ≡ E [ e ] → 
      send (val v₁) e₂ ≡ sendr-E v₁ E [ e ]
    call-≡ : ∀{τ φ}{e : Exp Δ Γ Ξ τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      fun （ args ） ≡ call-E fun E [ e ]
    spawn-≡ : ∀{τ φ}{e : Exp Δ Γ Ξ τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawn fun args ≡ spawn-E fun E [ e ]
    spawng-≡ : ∀{τ φ}{e : Exp Δ Γ Ξ τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawng fun args ≡ spawng-E fun E [ e ]
    ,-≡ : ∀{τ φ e₀}{e₁ : Exp Δ Γ Ξ τ}{E : E Δ Γ Ξ φ Un}{e : Exp Δ Γ Ξ φ} →  e₀ ≡ E [ e ] → 
      (e₀ , e₁) ≡ ,-E E e₁ [ e ]
    Let-≡ : ∀{ξ φ τ e₀}{e₁ : Exp Δ Γ (ξ ∷ Ξ) τ}{E : E Δ Γ Ξ φ ξ}{e : Exp Δ Γ Ξ φ} → e₀ ≡ E [ e ] → 
      (Let e₀ e₁) ≡ Let-E E e₁ [ e ]

data Call (Δ : FCtx) : Set where
   <_/_> : ∀{φ τ Γ} → E Δ Γ [] φ τ → State Γ → Call Δ

data Task (Δ : FCtx) : Set where
   ⟨_,_,_,_⟩ : Queue → ∀{Γ τ} → Exp Δ Γ [] τ → State Γ → List (Call Δ) → Task Δ

data Group (Δ : FCtx) : ℕ → Set where
  group : ∀{n} → Maybe (Fin n) → Vec (Task Δ) n → Group Δ n

data Cfg : ∀{n} → Vec ℕ n → Set where
    [] : Cfg []
    _∷_ : ∀{Δ m l}{n : Vec ℕ l} → Group Δ m → Cfg n → Cfg (m ∷ n)

data GroupE (Δ : FCtx) : (n : ℕ) → Fin n → Set where
  task-E : ∀{n} → Vec (Task Δ) n → GroupE Δ (suc n) zero
  tasks-E : ∀{n m} → Task Δ → GroupE Δ n m → GroupE Δ (suc n) (suc m)

data _≡G_[_] {Δ} : ∀{n}{m : Fin n} → Group Δ n → GroupE Δ n m → Task Δ → Set where
  head-≡G : ∀{n task}{tasks : Vec (Task Δ) n} → 
     group (just zero) (task ∷ tasks) ≡G task-E tasks [ task ]
  tail-≡G : ∀{task task´ n x}{tasks : Vec (Task Δ) n}{m : Fin n}{E : GroupE Δ n m} → 
     group (just x) tasks ≡G E [ task ] → 
     group (just (suc x)) (task´ ∷ tasks) ≡G tasks-E task´ E [ task ]

data CfgE : ∀{n} → Fin n → Vec ℕ n → Set where
  head-E : ∀{n t}{T : Vec ℕ n} → Cfg T → CfgE zero (t ∷ T)
  tail-E : ∀{n m t}{T : Vec ℕ n}{Δ : FCtx} → Group Δ t → CfgE m T → CfgE (suc m) (t ∷ T)

data _≡C_[_] {Δ} : ∀{n x}{T : Vec ℕ n} → Cfg T → CfgE x T → Group Δ (lookup x T) → Set where
  head-≡C : ∀{n t}{T : Vec ℕ n}{cfg : Cfg T}{g : Group Δ t} →
    (g ∷ cfg) ≡C head-E cfg [ g ]
  tail-≡E : ∀{n x t}{T : Vec ℕ n}{cfg : Cfg T}{g' : Group Δ t}{E : CfgE x T}{g : Group Δ (lookup x T)} → 
    cfg ≡C E [ g ] → 
    (g' ∷ cfg) ≡C tail-E g' E [ g ]
