module Source.EvalCtx where

open import Data.Nat
open import Data.Fin
-- open import Data.Vec hiding (group)
open import Data.List
open import Data.Maybe
open import Data.Product

open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Source.Syntax
open import Util.Vector

-- evaluation ctx, indexed by the type of the hole and the return type
data E (Δ : FCtx)(Γ : Ctx)(Ξ : CCtx) (T : TCtx) : Type → Type → Set

data FunE (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) (T : TCtx) : Ctx → Set where
    empty : FunE Δ Γ Ξ T []
    val : ∀{φ Φ} → Val T φ → FunE Δ Γ Ξ T Φ → FunE Δ Γ Ξ T (φ ∷ Φ)
    exp : ∀{τ φ Φ} → E Δ Γ Ξ T τ φ → ExpList Δ Γ Ξ T Φ → FunE Δ Γ Ξ T (φ ∷ Φ)

-- Eval ctx : variable context, var ctx that goes in the hole, function context, type expected in the hole, return type
data E (Δ : FCtx)(Γ : Ctx)(Ξ : CCtx)(T : TCtx) where
    □  : ∀{τ} → E Δ Γ Ξ T τ τ
    ¬-E : ∀{τ} → E Δ Γ Ξ T τ Bo → E Δ Γ Ξ T τ Bo                              -- ¬ E
    ∨l-E : ∀{τ} → E Δ Γ Ξ T τ Bo → Exp Δ Γ Ξ T Bo → E Δ Γ Ξ T τ Bo                 -- E ∨ e  
    ∨r-E : ∀{τ} → Val T Bo → E Δ Γ Ξ T τ Bo → E Δ Γ Ξ T τ Bo -- v ∨ E            -- what about true ∨ E ?
    =l-E : ∀{A B} → E Δ Γ Ξ T A B → Exp Δ Γ Ξ T B → E Δ Γ Ξ T A Bo                 -- E = e
    =r-E : ∀{A B} → Val T B → E Δ Γ Ξ T A B → E Δ Γ Ξ T A Bo -- v = E
    +l-E : ∀{A} → E Δ Γ Ξ T A In → Exp Δ Γ Ξ T In → E Δ Γ Ξ T A In                 -- E + e  
    +r-E : ∀{A} → Val T In → E Δ Γ Ξ T A In → E Δ Γ Ξ T A In -- v + E
    
    call-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Ξ T Λ → E Δ Γ Ξ T A τ
    spawn-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Ξ T Λ → E Δ Γ Ξ T A AR
    spawng-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Ξ T Λ → E Δ Γ Ξ T A AR

    ≔-E : ∀{A τ} → (v : Var Γ τ) → E Δ Γ Ξ T A τ → E Δ Γ Ξ T A Un      -- x ≔ E
    ,-E : ∀{A B} → E Δ Γ Ξ T A Un → Exp Δ Γ Ξ T B → E Δ Γ Ξ T A B                 -- E , e
    if-E : ∀{A B} → E Δ Γ Ξ T A Bo → Exp Δ Γ Ξ T B → Exp Δ Γ Ξ T B → E Δ Γ Ξ T A B     -- If E then e else e
    ignore-E : ∀{A B} → E Δ Γ Ξ T A B → E Δ Γ Ξ T A Un -- ignore E
    sendl-E : ∀{A B} → E Δ Γ Ξ T A AR → Exp Δ Γ Ξ T B → E Δ Γ Ξ T A B                 -- send E e
    sendr-E : ∀{A B} → Val T AR → E Δ Γ Ξ T A B → E Δ Γ Ξ T A B -- send v E
    Let-E : ∀{A σ τ} → E Δ Γ Ξ T A σ → Exp Δ Γ (σ ∷ Ξ) T τ → E Δ Γ Ξ T A τ -- let E e

infix 4 _≡_[_]
infix 4 _≡′_[_]

data _≡_[_] {Γ Δ Ξ T} : ∀{τ φ} → Exp Δ Γ Ξ T τ → E Δ Γ Ξ T φ τ → Exp Δ Γ Ξ T φ → Set

data _≡′_[_] {Γ Δ Ξ T} : ∀{φ ctx} → ExpList Δ Γ Ξ T ctx → FunE Δ Γ Ξ T ctx → Exp Δ Γ Ξ T φ → Set where
    exp-≡′ : ∀{ctx φ}{e' : Exp Δ Γ Ξ T φ}{τ}{E : E Δ Γ Ξ T φ τ}{e}{l : ExpList Δ Γ Ξ T ctx} → 
         e ≡ E [ e' ] → 
         e ∷ l ≡′ exp E l [ e' ]
    val-≡′ : ∀{ctx l}{E : FunE Δ Γ Ξ T ctx}{τ}{v : Val T τ}{φ}{e : Exp Δ Γ Ξ T φ} → 
         l ≡′ E [ e ] → 
         (val v) ∷ l ≡′ val v E [ e ]

data _≡_[_] {Γ Δ Ξ T} where
    exp-≡ : ∀{τ} {e : Exp Δ Γ Ξ T τ} → -- e redex →
      e ≡ □ [ e ]
    =l-≡ : ∀{τ φ E} {e₀ e₁ : Exp Δ Γ Ξ T τ} {e : Exp Δ Γ Ξ T φ} → e₀ ≡ E [ e ] → 
      e₀ ≐ e₁ ≡ =l-E E e₁ [ e ]
    =r-≡ : ∀{A B E} {e₀ : Val T A} {e₁ : Exp Δ Γ Ξ T A} {e : Exp Δ Γ Ξ T B} → e₁ ≡ E [ e ] → 
      val e₀ ≐ e₁ ≡ =r-E e₀ E [ e ]
    ¬-≡ : ∀{B E} {e₀ : Exp Δ Γ Ξ T Bo}{e : Exp Δ Γ Ξ T B} → e₀ ≡ E [ e ] → 
      ¬ e₀ ≡ ¬-E E [ e ]
    +l-≡ : ∀{B E} {e₀ e₁ : Exp Δ Γ Ξ T In} {e : Exp Δ Γ Ξ T B} → e₀ ≡ E [ e ] → 
      e₀ ∔ e₁ ≡ +l-E E e₁ [ e ]
    +r-≡ : ∀{B E} {e₀ : Val T In} {e₁ : Exp Δ Γ Ξ T In} {e : Exp Δ Γ Ξ T B} → e₁ ≡ E [ e ] → 
      val e₀ ∔ e₁ ≡ +r-E e₀ E [ e ]
    ∨l-≡ : ∀{B E} {e₀ e₁ : Exp Δ Γ Ξ T Bo} {e : Exp Δ Γ Ξ T B} → e₀ ≡ E [ e ] → 
      e₀ ⊻ e₁ ≡ ∨l-E E e₁ [ e ]
    ∨r-≡ : ∀{B E} {e₀ : Val T Bo} {e₁ : Exp Δ Γ Ξ T Bo} {e : Exp Δ Γ Ξ T B} → e₁ ≡ E [ e ] → 
      val e₀ ⊻ e₁ ≡ ∨r-E e₀ E [ e ]
    ≔-≡ : ∀{τ φ} {x : Var Γ φ} {e₀ : Exp Δ Γ Ξ T φ}{e : Exp Δ Γ Ξ T τ} {E : E Δ Γ Ξ T τ φ} → e₀ ≡ E [ e ] → 
      x ≔ e₀ ≡ ≔-E x E [ e ]
    if-≡ : ∀{A B E e₀} {e₁ e₂ : Exp Δ Γ Ξ T A} {e : Exp Δ Γ Ξ T B} → e₀ ≡ E [ e ] → 
      If e₀ then e₁ else e₂ ≡ if-E E e₁ e₂ [ e ]
    ignore-≡ : ∀{A B E} {e₀ : Exp Δ Γ Ξ T A}{e : Exp Δ Γ Ξ T B} → e₀ ≡ E [ e ] → 
      ignore e₀ ≡ ignore-E E [ e ]
    sendl-≡ : ∀{A B E e₁} {e₂ : Exp Δ Γ Ξ T B}{e : Exp Δ Γ Ξ T A} → e₁ ≡ E [ e ] →
      send e₁ e₂ ≡ sendl-E E e₂ [ e ]
    sendr-≡ : ∀{A B E v₁} {e₂ : Exp Δ Γ Ξ T B} {e : Exp Δ Γ Ξ T A} → e₂ ≡ E [ e ] → 
      send (val v₁) e₂ ≡ sendr-E v₁ E [ e ]
    call-≡ : ∀{τ φ}{e : Exp Δ Γ Ξ T τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      fun （ args ） ≡ call-E fun E [ e ]
    spawn-≡ : ∀{τ φ}{e : Exp Δ Γ Ξ T τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawn fun args ≡ spawn-E fun E [ e ]
    spawng-≡ : ∀{τ φ}{e : Exp Δ Γ Ξ T τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawng fun args ≡ spawng-E fun E [ e ]
    ,-≡ : ∀{τ φ e₀}{e₁ : Exp Δ Γ Ξ T τ}{E : E Δ Γ Ξ T φ Un}{e : Exp Δ Γ Ξ T φ} →  e₀ ≡ E [ e ] → 
      (e₀ , e₁) ≡ ,-E E e₁ [ e ]
    Let-≡ : ∀{ξ φ τ e₀}{e₁ : Exp Δ Γ (ξ ∷ Ξ) T τ}{E : E Δ Γ Ξ T φ ξ}{e : Exp Δ Γ Ξ T φ} → e₀ ≡ E [ e ] → 
      (Let e₀ e₁) ≡ Let-E E e₁ [ e ]

data Call (Δ : FCtx)(T : TCtx) : Set where
   <_/_> : ∀{φ τ Γ} → E Δ Γ [] T φ τ → State T Γ → Call Δ T

data Task (Δ : FCtx)(T : TCtx) : Set where
   ⟨_,_,_,_⟩ : Queue T → ∀{Γ τ} → Exp Δ Γ [] T τ → State T Γ → List (Call Δ T) → Task Δ T

--data Group (Δ : FCtx)(T : TCtx)(n : Fin (proj₁ T)) : Set where
data Group (Δ : FCtx)(T : TCtx)(len : ℕ) : Set where
  group-busy : ∀{m} → Vec (Task Δ T) zero m → Task Δ T → Vec (Task Δ T) (suc m) len → Group Δ T len
  group-idle : Vec (Task Δ T) zero len → Group Δ T len

data GroupE (Δ : FCtx)(T : TCtx) : (n : ℕ) → Set where
  group-E : ∀{n m} → Vec (Task Δ T) zero m → Vec (Task Δ T) (suc m) n → GroupE Δ T n

data _≡G_[_] {Δ T n} : Group Δ T n → GroupE Δ T n → Task Δ T → Set where -- (lookup n (proj₂ T)) → Task Δ T → Set where
   group-≡G : ∀{m task}{tasks₁ : Vec (Task Δ T) zero m}{tasks₂} → 
     group-busy tasks₁ task tasks₂ ≡G group-E tasks₁ tasks₂ [ task ]

data Cfg' {Δ} (T : TCtx) : (T' : TCtx) → Fin (suc (proj₁ T')) → Set where
  [] : Cfg' T (zero , []) zero
  _∷_ : ∀{n N l idx} → Group Δ T l → Cfg' {Δ} T (n , N) idx → Cfg' T (suc n , (l ∷ N)) (suc idx)

maxidx : ∀{n} → Fin (suc n)
maxidx {zero} = zero
maxidx {suc n} = suc (maxidx {n})

Cfg : ∀{Δ} (T : TCtx) → Set
Cfg {Δ} T = Cfg' {Δ} T T maxidx

data CfgE' (Δ : FCtx)(T : TCtx) : (T' : TCtx) → Fin (proj₁ T') → Set where
  head-E : ∀{n l idx}{T' : Vec ℕ 0 l} → Cfg' {Δ} T (_ , T') idx → CfgE' Δ T (suc _ , n ∷ T') idx
  tail-E : ∀{n l idx}{T' : Vec ℕ 0 l} → Group Δ T n → CfgE' Δ T (_ , T') idx → CfgE' Δ T (suc _ , (n ∷ T')) (inject₁ idx)

CfgE : FCtx → (T : TCtx) → Fin (proj₁ T) → Set
CfgE Δ T idx = CfgE' Δ T T idx

max-cfg' : ∀{Δ T m v idx}{T' : Vec ℕ zero m} → Cfg' {Δ} T (suc _ , v ∷ T') idx → idx == suc (lastidx (v ∷ T'))
max-cfg' (_ ∷ [])        = refl
max-cfg' (_ ∷ (x ∷ cfg)) = cong suc (max-cfg' (x ∷ cfg))

suc-eq : ∀{m}{a b : Fin m} → _==_ {A = Fin (suc m)} (suc a) (suc b) → a == b
suc-eq refl = refl

down-idx : ∀{Δ T T' idx} → (v : ℕ) → Cfg' {Δ} T T' idx → v == lookup idx (v ∷ proj₂ T')
down-idx _ [] = refl
down-idx {idx = suc idx} _ (_∷_ {N = N'} {l = l} x cfg') rewrite suc-eq (max-cfg' {idx = suc idx} (x ∷ cfg')) | down-lastidx {x = l} (l ∷ N') = refl

inject-idx : ∀{A : Set}{n}{v : A}{T : Vec A zero n} → (idx : Fin n) → lookup idx T == lookup (inject₁ idx) (v ∷ T)
inject-idx idx rewrite down-inject idx = refl

data _≡C_[_] {Δ T} : ∀{T' n idx} → Cfg' {Δ} T T' n → CfgE' Δ T T' idx → Group Δ T (lookup idx (proj₂ T')) → Set where
  head-≡C : ∀{T' idx}{len : ℕ} →
    {C : Cfg' {Δ} T T' idx} →
    {g : Group Δ T len} → 
    (g ∷ C) ≡C head-E C [ subst (Group Δ T) (down-idx len C) g ]
  tail-≡C : ∀{T' idx idx' len} → 
    {C : Cfg' T T' idx} → 
    {g : Group Δ T len} → -- (lookup idx (len ∷ proj₂ T'))} → 
    {E : CfgE' Δ T T' idx'} →
    {g' : Group Δ T (lookup idx' (proj₂ T'))} → 
    C ≡C E [ g' ] → 
    (g ∷ C) ≡C tail-E g E [ subst (Group Δ T) (inject-idx idx') g' ]
