module Source where

open import Data.Bool
open import Data.Unit 
open import Data.List
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (_++_; group)
open import Data.Product
open import Data.Sum

open import Data.Maybe

infixr 5 _∷_

_≡b_ : Bool → Bool → Bool
true  ≡b true  = true
false ≡b false = true
_     ≡b _     = false

_≡n_ : ℕ → ℕ → Bool
zero    ≡n zero    = true
zero    ≡n (suc _) = false
(suc _) ≡n zero    = false
(suc a) ≡n (suc b) = a ≡n b

-- base types
data Type : Set where
  Un : Type
  Bo : Type
  In : Type
  AR : Type

GroupID : Set
GroupID = ℕ

TaskID : Set
TaskID = ℕ

-- actor references: identifies the group and the task
data ARef : Set where
  AR : GroupID → TaskID → ARef

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
    A : ARef → Val AR
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

mutual
  -- list of expressions
  data ExpList (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) : Ctx → Set where
    [] : ExpList Δ Γ Ξ []
    _∷_ : ∀{τ T} → Exp Δ Γ Ξ τ → ExpList Δ Γ Ξ T → ExpList Δ Γ Ξ (τ ∷ T)

  data Exp (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) : Type → Set where
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

data _redex {Γ Δ Ξ} : ∀{τ} → Exp Δ Γ Ξ τ → Set where
  var-redex     : ∀{τ}{v : Var Γ τ} → (var v) redex
  =-redex       : ∀{τ}{v₁ v₂ : Val τ} → ((val v₁) ≐ (val v₂)) redex
  +-redex       : ∀{v₁ v₂} → (val v₁ ∔ val v₂) redex
  ∨-redex       : ∀{v₁ v₂} → (val v₁ ⊻ val v₂) redex
  ¬-redex       : ∀{v} → (¬ val v) redex
  avail-redex   : avail redex
  ≔-redex       : ∀{τ v}{x : Var Γ τ} → (x ≔ val v) redex
  skip-redex    : skip redex
  ,-redex       : ∀{τ}{e : Exp Δ Γ Ξ τ} → (val U , e) redex
  ignore-redex  : ∀{τ}{v : Val τ} → ignore (val v) redex
  if-redex      : ∀{τ v}{e₁ e₂ : Exp Δ Γ Ξ τ} → (If (val v) then e₁ else e₂) redex
  while-redex   : ∀{e₀}{e : Exp Δ Γ Ξ Un} → (While e₀ do e) redex
  send-redex    : ∀{τ v₁}{v₂ : Val τ} → send (val v₁) (val v₂) redex
  receive-redex : ∀{τ}{e₁ : Exp Δ Γ (Un ∷ Ξ) τ}{e₂ : Exp Δ Γ (AR ∷ Ξ) τ}{e₃ : Exp Δ Γ (In ∷ Ξ) τ}{e₄ : Exp Δ Γ (Bo ∷ Ξ) τ} → receive e₁ e₂ e₃ e₄ redex
  call-redex    : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (fun （ args ）) redex
  spawn-redex   : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (spawn fun args) redex
  spawng-redex  : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (spawng fun args) redex
  yield-redex   : yield redex
  Let-redex     : ∀{τ ξ}{v : Val ξ}{e : Exp Δ Γ (ξ ∷ Ξ) τ} → Let (val v) e redex


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

-- evaluation ctx, indexed by the type of the hole and the return type
mutual

  data FunE (Δ : FCtx) (Γ : Ctx) (Ξ : CCtx) : Ctx → Set where
    empty : FunE Δ Γ Ξ []
    val : ∀{φ Φ} → Val φ → FunE Δ Γ Ξ Φ → FunE Δ Γ Ξ (φ ∷ Φ)
    exp : ∀{τ φ Φ} → E Δ Γ Ξ τ φ → ExpList Δ Γ Ξ Φ → FunE Δ Γ Ξ (φ ∷ Φ)

  -- Eval ctx : variable context, var ctx that goes in the hole, function context, type expected in the hole, return type
  data E (Δ : FCtx)(Γ : Ctx)(Ξ : CCtx) : Type → Type → Set where
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

mutual
  data _≡′_[_] {Γ Δ Ξ} : ∀{φ ctx} → ExpList Δ Γ Ξ ctx → FunE Δ Γ Ξ ctx → Exp Δ Γ Ξ φ → Set where
    exp-≡′ : ∀{ctx φ}{e' : Exp Δ Γ Ξ φ}{τ}{E : E Δ Γ Ξ φ τ}{e}{l : ExpList Δ Γ Ξ ctx} → 
         e ≡ E [ e' ] → 
         e ∷ l ≡′ exp E l [ e' ]
    val-≡′ : ∀{ctx l}{E : FunE Δ Γ Ξ ctx}{τ}{υ : Val τ}{φ}{e : Exp Δ Γ Ξ φ} → 
         l ≡′ E [ e ] → 
         (val υ) ∷ l ≡′ val υ E [ e ]

  data _≡_[_] {Γ Δ Ξ} : ∀{τ φ} → Exp Δ Γ Ξ τ → E Δ Γ Ξ φ τ → Exp Δ Γ Ξ φ → Set where
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


data EnvF' (Δ : FCtx) : FCtx → Set where
 [] : EnvF' Δ []
 _∷_ : ∀{Γ φ Φ} → Exp Δ Γ [] φ → EnvF' Δ Φ → EnvF' Δ ((Γ , φ) ∷ Φ)

EnvF : FCtx → Set
EnvF Δ = EnvF' Δ Δ

data Call (Δ : FCtx) : Set where
  <_/_> : ∀{φ τ Γ} → E Δ Γ [] φ τ → State Γ → Call Δ

data Task (Δ : FCtx) : Set where
  ⟨_,_,_,_⟩ : Queue → ∀{Γ τ} → Exp Δ Γ [] τ → State Γ → List (Call Δ) → Task Δ

data Group (Δ : FCtx) : ℕ → Set where
  group : ∀{n} → Maybe (Fin n) → Vec (Task Δ) n → Group Δ n

-- indexed by the number of groups
Cfg : FCtx → ℕ → Set
Cfg Δ n = Vec (∃ λ m → Group Δ m) n

lkp-fun : ∀{Δ Γ' Δ' τ} → EnvF' Δ' Δ → (f : Fun Δ Γ' τ) → Exp Δ' Γ' [] τ
lkp-fun []         ()
lkp-fun (f ∷ _)    (z ._ ._) = f
lkp-fun (_ ∷ envF) (s fun)   = lkp-fun envF fun

a2s' : ∀{Γ Δ Ξ Γ'} → (args : ExpList Γ Δ Ξ Γ') → args values → State Γ'
a2s' []          []-values = []
a2s' (._ ∷ args) (∷-values va ._ p) = va ∷ a2s' args p

args-to-state : ∀{τ Γ Ξ Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ Λ) → fun （ args ） redex → State Λ
args-to-state fun args (call-redex x) = a2s' args x

spawn-args-to-state : ∀{τ Γ Ξ Δ Γ'} → (fun : Fun Δ Γ' τ) → (args : ExpList Δ Γ Ξ Γ') → spawn fun args redex → State Γ'
spawn-args-to-state fun args (spawn-redex x) = a2s' args x

spawng-args-to-state : ∀{τ Γ Ξ Δ Γ'} → (fun : Fun Δ Γ' τ) → (args : ExpList Δ Γ Ξ Γ') → spawng fun args redex → State Γ'
spawng-args-to-state fun args (spawng-redex x) = a2s' args x

{-
ren-const' : ∀{φ ξ τ} → (Ψ Ξ : CCtx) → Const (Ψ ++ (φ ∷ ξ ∷ Ξ)) τ → Const (Ψ ++ (ξ ∷ φ ∷ Ξ)) τ
ren-const' []       Ξ (z ._) = s (z _)
ren-const' []       Ξ (s (z ._)) = z _
ren-const' []       Ξ (s (s c)) = s (s c)
ren-const' (._ ∷ Ψ) Ξ (z ._) = z _
ren-const' (_ ∷ Ψ)  Ξ (s c) = s (ren-const' Ψ Ξ c)


ren-const : ∀{Δ Γ ψ τ ξ} → (Ψ Ξ : CCtx) → Exp Δ Γ (Ψ ++ (ψ ∷ ξ ∷ Ξ)) τ → Exp Δ Γ (Ψ ++ (ξ ∷ ψ ∷ Ξ)) τ

ren-const-list : ∀{Δ Γ Λ ψ ξ} → (Ψ Ξ : CCtx) → ExpList Δ Γ (Ψ ++ (ψ ∷ ξ ∷ Ξ)) Λ → ExpList Δ Γ (Ψ ++ (ξ ∷ ψ ∷ Ξ)) Λ
ren-const-list Ψ Ξ [] = []
ren-const-list Ψ Ξ (e ∷ es) = ren-const Ψ Ξ e ∷ ren-const-list Ψ Ξ es 

ren-const Ψ Ξ (var x) = var x
ren-const Ψ Ξ (val x) = val x
ren-const Ψ Ξ (const x) = const (ren-const' Ψ Ξ x)
ren-const Ψ Ξ (e ≐ e₁) = ren-const Ψ Ξ e ≐ ren-const Ψ Ξ e₁
ren-const Ψ Ξ (¬ e) = ¬ ren-const Ψ Ξ e
ren-const Ψ Ξ (e ∔ e₁) = ren-const Ψ Ξ e ∔ ren-const Ψ Ξ e₁
ren-const Ψ Ξ (e ⊻ e₁) = ren-const Ψ Ξ e ⊻ ren-const Ψ Ξ e₁
ren-const Ψ Ξ avail = avail
ren-const Ψ Ξ (f （ args ）) = f （ ren-const-list Ψ Ξ args ）
ren-const Ψ Ξ (spawn f args) = spawn f (ren-const-list Ψ Ξ args)
ren-const Ψ Ξ (spawng f args) = spawng f (ren-const-list Ψ Ξ args)
ren-const Ψ Ξ yield = yield
ren-const Ψ Ξ (x ≔ e) = x ≔ ren-const Ψ Ξ e
ren-const Ψ Ξ skip = skip
ren-const Ψ Ξ (e , e₁) = ren-const Ψ Ξ e , ren-const Ψ Ξ e₁
ren-const Ψ Ξ (If e then e₁ else e₂) = If ren-const Ψ Ξ e then ren-const Ψ Ξ e₁ else ren-const Ψ Ξ e₂
ren-const Ψ Ξ (While e do e₁) = While ren-const Ψ Ξ e do ren-const Ψ Ξ e₁
ren-const Ψ Ξ (send e e₁) = send (ren-const Ψ Ξ e) (ren-const Ψ Ξ e₁)
ren-const Ψ Ξ (receive e e₁ e₂ e₃) = receive (ren-const (_ ∷ Ψ) Ξ e) (ren-const (_ ∷ Ψ) Ξ e₁) (ren-const (_ ∷ Ψ) Ξ e₂) (ren-const (_ ∷ Ψ) Ξ e₃)
ren-const Ψ Ξ (ignore e) = ignore (ren-const Ψ Ξ e)
ren-const Ψ Ξ (Let e e₁) = Let (ren-const Ψ Ξ e) (ren-const (_ ∷ Ψ) Ξ e₁)

ren-const₂ : ∀{Ξ Δ Γ ψ τ ξ} → Exp Δ Γ (ψ ∷ ξ ∷ Ξ) τ → Exp Δ Γ (ξ ∷ ψ ∷ Ξ) τ
ren-const₂ {Ξ} ex = ren-const [] Ξ ex
-}
{-
subst-const : ∀{Δ Γ ξ τ} → (Ξ : CCtx) → Val ξ → Exp Δ Γ (ξ ∷ Ξ) τ → Exp Δ Γ Ξ τ

subst-const-list : ∀{Δ Γ ξ Λ} → (Ξ : CCtx) → Val ξ → ExpList Δ Γ (ξ ∷ Ξ) Λ → ExpList Δ Γ Ξ Λ
subst-const-list Ξ v [] = []
subst-const-list Ξ v (e ∷ es) = subst-const Ξ v e ∷ subst-const-list Ξ v es

subst-const Ξ v (var x) = var x
subst-const Ξ v (val x) = val x

subst-const Ξ v (const (z ._)) = val v
subst-const Ξ v (const (s x)) = const x

subst-const Ξ v (e ≐ e₁) = subst-const Ξ v e ≐ subst-const Ξ v e₁
subst-const Ξ v (¬ e) = ¬ subst-const Ξ v e
subst-const Ξ v (e ∔ e₁) = subst-const Ξ v e ∔ subst-const Ξ v e₁
subst-const Ξ v (e ⊻ e₁) = subst-const Ξ v e ⊻ subst-const Ξ v e₁
subst-const Ξ v avail = avail
subst-const Ξ v (f （ args ）) = f （ subst-const-list Ξ v args ）
subst-const Ξ v (spawn f args) = spawn f (subst-const-list Ξ v args)
subst-const Ξ v (spawng f args) = spawng f (subst-const-list Ξ v args)
subst-const Ξ v yield = yield
subst-const Ξ v (x ≔ e) = x ≔ subst-const Ξ v e
subst-const Ξ v skip = skip
subst-const Ξ v (e , e₁) = subst-const Ξ v e , subst-const Ξ v e₁
subst-const Ξ v (If e then e₁ else e₂) = If subst-const Ξ v e then subst-const Ξ v e₁ else subst-const Ξ v e₂
subst-const Ξ v (While e do e₁) = While subst-const Ξ v e do subst-const Ξ v e₁
subst-const Ξ v (send e e₁) = send (subst-const Ξ v e) (subst-const Ξ v e₁)
subst-const Ξ v (receive e e₁ e₂ e₃) = receive {!!} {!!} {!!} {!!}
subst-const Ξ v (ignore e) = ignore (subst-const Ξ v e)
subst-const Ξ v (Let e e₁) = Let (subst-const Ξ v e) {!!} -- (subst-const (_ ∷ Ξ) v (ren-const₂ e₁))
-}

--sc-idx : (Ψ : Vec Type n) → Val (lookup m Ψ) → Const Ψ τ → Exp Δ Γ ? τ
{-
sc : ∀{Δ Γ Ξ ξ τ} → (Ψ : CCtx) → Const (Ψ ++ (ξ ∷ Ξ)) ξ → Val ξ → Const (Ψ ++ (ξ ∷ Ξ)) τ → Exp Δ Γ (Ψ ++ Ξ) τ
sc [] c v e = {!!}
sc {Δ} {Γ} {Ξ} {.τ} {τ} (.τ ∷ Ψ) (z .τ) v (z .τ) = val v
sc {Δ} {Γ} {Ξ} {ξ} (.ξ ∷ Ψ) (z .ξ) v (s e) = {!const e!}
sc (x ∷ Ψ) (s c) v e = {!!}

subst-const' : ∀{Δ Γ τ ξ} → (Ψ Ξ : CCtx) → Const (Ψ ++ (ξ ∷ Ξ)) ξ → Val ξ → Exp Δ Γ (Ψ ++ (ξ ∷ Ξ)) τ → Exp Δ Γ (Ψ ++ Ξ) τ

subst-const-list' : ∀{Δ Γ Λ ξ} → (Ψ Ξ : CCtx) → Const (Ψ ++ (ξ ∷ Ξ)) ξ → Val ξ → ExpList Δ Γ (Ψ ++ (ξ ∷ Ξ)) Λ → ExpList Δ Γ (Ψ ++ Ξ) Λ
subst-const-list' Ψ Ξ c v [] = []
subst-const-list' Ψ Ξ c v (e ∷ el) = subst-const' Ψ Ξ c v e ∷ subst-const-list' Ψ Ξ c v el

subst-const' Ψ Ξ c v (var x) = var x
subst-const' Ψ Ξ c v (val x) = val x

subst-const' Ψ Ξ c v (const x₁) = {!!}

subst-const' Ψ Ξ c v (e ≐ e₁) = subst-const' Ψ Ξ c v e ≐ subst-const' Ψ Ξ c v e₁
subst-const' Ψ Ξ c v (¬ e) = ¬ subst-const' Ψ Ξ c v e
subst-const' Ψ Ξ c v (e ∔ e₁) = subst-const' Ψ Ξ c v e ∔ subst-const' Ψ Ξ c v e₁
subst-const' Ψ Ξ c v (e ⊻ e₁) = subst-const' Ψ Ξ c v e ⊻ subst-const' Ψ Ξ c v e₁
subst-const' Ψ Ξ c v avail = avail
subst-const' Ψ Ξ c v (f （ args ）) = f （ subst-const-list' Ψ Ξ c v args ）
subst-const' Ψ Ξ c v (spawn f args) = spawn f (subst-const-list' Ψ Ξ c v args)
subst-const' Ψ Ξ c v (spawng f args) = spawng f (subst-const-list' Ψ Ξ c v args)
subst-const' Ψ Ξ c v yield = yield
subst-const' Ψ Ξ c v (x ≔ e) = x ≔ subst-const' Ψ Ξ c v e
subst-const' Ψ Ξ c v skip = skip
subst-const' Ψ Ξ c v (e , e₁) = subst-const' Ψ Ξ c v e , subst-const' Ψ Ξ c v e₁
subst-const' Ψ Ξ c v (If e then e₁ else e₂) = If subst-const' Ψ Ξ c v e then subst-const' Ψ Ξ c v e₁ else subst-const' Ψ Ξ c v e₂
subst-const' Ψ Ξ c v (While e do e₁) = While subst-const' Ψ Ξ c v e do subst-const' Ψ Ξ c v e₁
subst-const' Ψ Ξ c v (send e e₁) = send (subst-const' Ψ Ξ c v e) (subst-const' Ψ Ξ c v e₁)
subst-const' Ψ Ξ c v (receive e e₁ e₂ e₃) = receive (subst-const' (Un ∷ Ψ) Ξ (s c) v e) (subst-const' (AR ∷ Ψ) Ξ (s c) v e₁) (subst-const' (In ∷ Ψ) Ξ (s c) v e₂) (subst-const' (Bo ∷ Ψ) Ξ (s c) v e₃)
subst-const' Ψ Ξ c v (ignore e) = ignore (subst-const' Ψ Ξ c v e)
subst-const' Ψ Ξ c v (Let e e₁) = Let (subst-const' Ψ Ξ c v e) (subst-const' (_ ∷ Ψ) Ξ (s c) v e₁)
-}

Ren : CCtx → CCtx → Set
Ren Φ Ψ = ∀{τ} → Const Φ τ → Const Ψ τ

wk : ∀{Φ Ψ τ} → Ren Φ Ψ → Ren (τ ∷ Φ) (τ ∷ Ψ)
wk f (z ._) = z _
wk f (s v) = s (f v)

ren : ∀{Δ Γ Φ Ψ τ} → Ren Φ Ψ → Exp Δ Γ Φ τ → Exp Δ Γ Ψ τ

ren-args : ∀{Δ Γ Φ Ψ Λ} → Ren Φ Ψ → ExpList Δ Γ Φ Λ → ExpList Δ Γ Ψ Λ
ren-args f [] = []
ren-args f (x ∷ el) = ren f x ∷ ren-args f el

ren f (var x) = var x
ren f (val x) = val x
ren f (const x) = const (f x)
ren f (tm ≐ tm₁) = ren f tm ≐ ren f tm₁
ren f (¬ tm) = ¬ ren f tm
ren f (tm ∔ tm₁) = ren f tm ∔ ren f tm₁
ren f (tm ⊻ tm₁) = ren f tm ⊻ ren f tm₁
ren f avail = avail
ren f (fun （ args ）) = fun （ ren-args f args ）
ren f (spawn fun args) = spawn fun (ren-args f args)
ren f (spawng fun args) = spawng fun (ren-args f args)
ren f yield = yield
ren f (x ≔ tm) = x ≔ ren f tm
ren f skip = skip
ren f (tm , tm₁) = ren f tm , ren f tm₁
ren f (If tm then tm₁ else tm₂) = If ren f tm then ren f tm₁ else ren f tm₂
ren f (While tm do tm₁) = While ren f tm do ren f tm₁
ren f (send tm tm₁) = send (ren f tm) (ren f tm₁)
ren f (receive tm tm₁ tm₂ tm₃) = receive (ren (wk f) tm) (ren (wk f) tm₁) (ren (wk f) tm₂) (ren (wk f) tm₃)
ren f (ignore tm) = ignore (ren f tm)
ren f (Let tm tm₁) = Let (ren f tm) (ren (wk f) tm₁)

Sub : FCtx → Ctx → CCtx → CCtx → Set
Sub Δ Γ Φ Ψ = ∀{τ} → Const Φ τ → Exp Δ Γ Ψ τ

lift-sub : ∀{Δ Γ Φ Ψ σ} → Sub Δ Γ Φ Ψ → Sub Δ Γ (σ ∷ Φ) (σ ∷ Ψ)
lift-sub f (z ._) = const (z _)
lift-sub f (s c) = ren s (f c)

sub : ∀{Δ Γ Φ Ψ τ} → Sub Δ Γ Φ Ψ → Exp Δ Γ Φ τ → Exp Δ Γ Ψ τ

sub-args : ∀{Δ Γ Φ Ψ Λ} → Sub Δ Γ Φ Ψ → ExpList Δ Γ Φ Λ → ExpList Δ Γ Ψ Λ
sub-args f [] = []
sub-args f (x ∷ el) = sub f x ∷ sub-args f el

sub f (var x) = var x
sub f (val x) = val x
sub f (const x) = f x 
sub f (e ≐ e₁) = sub f e ≐ sub f e₁
sub f (¬ e) = ¬ sub f e
sub f (e ∔ e₁) = sub f e ∔ sub f e₁
sub f (e ⊻ e₁) = sub f e ⊻ sub f e₁
sub f avail = avail
sub f (fun （ args ）) = fun （ sub-args f args ） 
sub f (spawn fun args) = spawn fun (sub-args f args)
sub f (spawng fun args) = spawng fun (sub-args f args)
sub f yield = yield
sub f (x ≔ e) = x ≔ sub f e
sub f skip = skip
sub f (e , e₁) = sub f e , sub f e₁
sub f (If e then e₁ else e₂) = If sub f e then sub f e₁ else sub f e₂
sub f (While e do e₁) = While sub f e do sub f e₁
sub f (send e e₁) = send (sub f e) (sub f e₁)
sub f (receive e e₁ e₂ e₃) = receive (sub (lift-sub f) e) (sub (lift-sub f) e₁) (sub (lift-sub f) e₂) (sub (lift-sub f) e₃)
sub f (ignore e) = ignore (sub f e)
sub f (Let e e₁) = Let (sub f e) (sub (lift-sub f) e₁)

_::_ : ∀{Δ Γ Φ Ψ τ} → Exp Δ Γ Ψ τ → Sub Δ Γ Φ Ψ → Sub Δ Γ (τ ∷ Φ) Ψ
(t :: f) (z ._) = t
(t :: f) (s e) = f e

subst-const : ∀{Δ Γ Ξ ξ τ} → Val ξ → Exp Δ Γ (ξ ∷ Ξ) τ → Exp Δ Γ Ξ τ
subst-const v e = sub (val v :: const) e

data _,_,_⟶e_,_,_ {Γ Δ Ξ} : ∀{τ} → Queue → Exp Δ Γ Ξ τ → State Γ → Queue → Exp Δ Γ Ξ τ → State Γ → Set where
  var↦ : ∀{q τ ρ}{v : Var Γ τ} → 
        q , var v                        , ρ ⟶e      q , val (lkp ρ v)       , ρ
  ∔↦ : ∀{q v₁ v₂ ρ} →
        q , (val (N v₁)) ∔ (val (N v₂)) , ρ ⟶e       q , val (N (v₁ + v₂))  , ρ
  ⊻↦ : ∀{q v₁ v₂ ρ} → 
         q , (val (B v₁)) ⊻ (val (B v₂))  , ρ ⟶e       q , val (B (v₁ ∨ v₂))  , ρ
  ¬↦ : ∀{q v ρ} →   
         q , ¬ (val (B v))                , ρ ⟶e       q , val (B (not v))    , ρ
  avail↦-true  : ∀{m q ρ} →  
   (m ∷ q) , avail                        , ρ ⟶e (m ∷ q) , val (B true)       , ρ
  avail↦-false : ∀{ρ} →
        [] , avail                        , ρ ⟶e      [] , val (B false)      , ρ
  ≐↦-int : ∀{q v₁ v₂ ρ} → 
         q , (val (N v₁)) ≐ (val (N v₂))  , ρ ⟶e       q , val (B (v₁ ≡n v₂)) , ρ
  ≐↦-bool : ∀{q v₁ v₂ ρ} →
         q , (val (B v₁)) ≐ (val (B v₂))  , ρ ⟶e       q , val (B (v₁ ≡b v₂)) , ρ
  skip↦ : ∀{q ρ} →
         q , skip                         , ρ ⟶e       q , val U              , ρ
  ≔⟶e : ∀{q τ v ρ}{x : Var Γ τ} →
         q , x ≔ val v                    , ρ ⟶e       q , val U              , upd x v ρ
  seq↦ : ∀{q ρ τ} {e : Exp Δ Γ Ξ τ} →
         q , (val U , e)                  , ρ ⟶e       q , e                  , ρ
  IfT↦ : ∀ {q ρ τ} {e₁ e₂ : Exp Δ Γ Ξ τ} → 
         q , If (val (B true)) then e₁ else e₂  , ρ ⟶e q , e₁ , ρ
  IfF↦ : ∀{q ρ τ} {e₁ e₂ : Exp Δ Γ Ξ τ} → 
         q , If (val (B false)) then e₁ else e₂ , ρ ⟶e q , e₂ , ρ
  While↦ : ∀{q e' e ρ} →
         q , While e do e'                      , ρ ⟶e q , If e then (e' , While e do e') else skip , ρ
  ignore↦ : ∀{q τ ρ}{v : Val τ} → 
         q , ignore (val v)                     , ρ ⟶e q , val U , ρ
  Let↦ : ∀{q ξ τ ρ}{v : Val ξ}{e : Exp Δ Γ (ξ ∷ Ξ) τ} → 
         q , Let (val v) e                      , ρ ⟶e q , subst-const v e , ρ
  Receive-Un⟶e : ∀{q τ ρ}{e₁ : Exp Δ Γ _ τ}{e₂ : Exp Δ Γ _ τ}{e₃ : Exp Δ Γ _ τ}{e₄ : Exp Δ Γ _ τ} → 
         ((Un , U) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val U) e₁ , ρ
  Receive-AR⟶e : ∀{q τ ρ x}{e₁ : Exp Δ Γ _ τ}{e₂ : Exp Δ Γ _ τ}{e₃ : Exp Δ Γ _ τ}{e₄ : Exp Δ Γ _ τ} → 
         ((AR , x) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val x) e₂ , ρ
  Receive-In⟶e : ∀{q τ ρ x}{e₁ : Exp Δ Γ _ τ}{e₂ : Exp Δ Γ _ τ}{e₃ : Exp Δ Γ _ τ}{e₄ : Exp Δ Γ _ τ} → 
         ((In , x) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val x) e₃ , ρ
  Receive-Bo⟶e : ∀{q τ ρ x}{e₁ : Exp Δ Γ _ τ}{e₂ : Exp Δ Γ _ τ}{e₃ : Exp Δ Γ _ τ}{e₄ : Exp Δ Γ _ τ} → 
         ((Bo , x) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val x) e₄ , ρ

data _⟶t_ {Δ} : Task Δ → Task Δ → Set where
  exp⟶t : ∀{Γ τ φ e₀ e₀' q q' ρ ρ' cs}{e e' : Exp Δ Γ [] τ}{E : E Δ Γ [] φ τ} → 
    e ≡ E [ e₀ ] → q , e₀ , ρ ⟶e q' , e₀' , ρ' → e' ≡ E [ e₀' ] → 
    ⟨ q , e , ρ , cs ⟩ ⟶t ⟨ q' , e' , ρ' , cs ⟩
  call⟶t : ∀{Γ Λ τ q ρ cs φ args E}{e : Exp Δ Γ [] τ}{f : Fun Δ Λ φ} → 
   (envF : EnvF Δ) → (p : f （ args ） redex) → e ≡ E [ f （ args ） ] → 
    ⟨ q , e , ρ , cs ⟩ ⟶t ⟨ q , lkp-fun envF f , args-to-state f args p , < E / ρ > ∷ cs ⟩
  return⟶t : ∀{Γ Γ' φ τ q}{ρ : State Γ'}{ρ' : State Γ}{cs}{e : Exp Δ Γ [] τ}{E : E Δ Γ [] φ τ}{v : Val φ} → 
    e ≡ E [ val v ] → 
    ⟨ q , val v , ρ , < E / ρ' > ∷ cs ⟩ ⟶t ⟨ q , e , ρ' , cs ⟩ 
 -- spawn, spawng, yield, send

data GroupE (Δ : FCtx) : (n : ℕ) → Fin n → Set where
  task-E : ∀{n} → Vec (Task Δ) n → GroupE Δ (suc n) zero
  tasks-E : ∀{n m} → Task Δ → GroupE Δ n m → GroupE Δ (suc n) (suc m)

data _≡G_[_] {Δ} : ∀{n}{m : Fin n} → Group Δ n → GroupE Δ n m → Task Δ → Set where
  head-≡G : ∀{n task}{tasks : Vec (Task Δ) n} → 
     group (just zero) (task ∷ tasks) ≡G task-E tasks [ task ]
  tail-≡G : ∀{task task´ n x}{tasks : Vec (Task Δ) n}{m : Fin n}{E : GroupE Δ n m} → 
     group (just x) tasks ≡G E [ task ] → 
     group (just (suc x)) (task´ ∷ tasks) ≡G tasks-E task´ E [ task ] 

send-local : ∀{Δ τ}{n : ℕ} → ℕ → Val τ → Vec (Task Δ) n → Vec (Task Δ) n
send-local zero    _ []                        = [] -- this should somehow be excluded
send-local zero    v (⟨ q , e , ρ , cs ⟩ ∷ ts) = ⟨ q Data.List.∷ʳ (_ , v) , e , ρ , cs ⟩ ∷ ts
send-local (suc _) _ []                        = [] -- this as well
send-local (suc n) v (x ∷ ts)                  = x ∷ send-local n v ts

data [_]_⟶g_ {Δ} : ∀{n n´} → ℕ → Group Δ n → Group Δ n´ → Set where
  step⟶g : ∀{gid task task´ n g g´}{m : Fin n}{E : GroupE Δ n m} → 
     task ⟶t task´ → 
     g ≡G E [ task ] → g´ ≡G E [ task´ ] → 
     [ gid ] g ⟶g g´
  yield⟶g : ∀{gid Γ n}{x : Fin n}{tasks tasks' : Vec (Task Δ) n}{τ}{e e' : Exp Δ Γ [] τ}{E₂ : E Δ Γ [] Un τ}{q ρ cs}{E : GroupE Δ n x} → 
    e ≡ E₂ [ yield ] → e' ≡ E₂ [ skip ] → 
    group (just x) tasks ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → group nothing tasks' ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] →   
    [ gid ] group (just x) tasks ⟶g group nothing tasks'
-- ?
  schedule⟶g : ∀{gid n}{tasks : Vec (Task Δ) n}{x : Fin n} → 
     [ gid ] group nothing tasks ⟶g group (just x) tasks
  spawn⟶g : ∀{Γ n}{x : Fin n}{tasks tasks' : Vec (Task Δ) n}{τ}{e e' : Exp Δ Γ [] τ}{E₂ : E Δ Γ [] AR τ}{q ρ cs}{E : GroupE Δ n x}{Λ φ}{f : Fun Δ Λ φ}{args gid} → 
    (envF : EnvF Δ) → (p : spawn f args redex) → 
    e ≡ E₂ [ spawn f args ] → e' ≡ E₂ [ val (A (AR gid n)) ] →
    group (just x) tasks ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → group (just x) tasks' ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] → 
    [ gid ] group (just x) tasks ⟶g group (just (inject₁ x)) (tasks Data.Vec.∷ʳ ⟨ [] , lkp-fun envF f  , spawn-args-to-state f args p  , [] ⟩)
  send-local⟶g : ∀{gid Γ n}{x : Fin n}{tasks tasks' : Vec (Task Δ) n}{τ φ}{e e' : Exp Δ Γ [] τ}{E₂ : E Δ Γ [] φ τ}{q ρ cs}{E : GroupE Δ n x}{recv msg} → 
    e ≡ E₂ [ send (val (A (AR gid recv))) (val msg) ] → e' ≡ E₂ [ val msg ] → 
    group (just x) tasks ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → group (just x) tasks' ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] →   
    [ gid ] group (just x) tasks ⟶g group (just x) (send-local recv msg tasks)

data CfgE (Δ : FCtx) : ℕ → ℕ → Set where
    head-E : ∀{n} → Cfg Δ n → CfgE Δ (suc n) zero
    tail-E : ∀{n m} → (∃ λ m → Group Δ m) → CfgE Δ n m → CfgE Δ (suc n) (suc m)

data _≡C_[_] {Δ} : ∀{n m} → Cfg Δ n → CfgE Δ n m → (∃ λ m → Group Δ m) → Set where
    head-≡C : ∀{m n}{group : Group Δ m}{groups : Cfg Δ n} → 
        ((m , group) ∷ groups) ≡C head-E groups [ m , group ]
    cfg-≡C : ∀{n m}{group groups}{E : CfgE Δ n m}{m g} → 
        groups ≡C E [ m , g ] → 
        (group ∷ groups) ≡C tail-E group E [ m , g ]

send-global : ∀{Δ τ}{n : ℕ} → ℕ → ℕ → Val τ → Cfg Δ n → Cfg Δ n
send-global grp task v [] = []
send-global zero task v ((n , group x ts) ∷ cfg) = (n , group x (send-local task v ts)) ∷ cfg
send-global (suc grp) task v (x ∷ cfg) = x ∷ send-global grp task v cfg

infixr 5 _⟶c_

data _⟶c_ {Δ} : ∀{n m} → Cfg Δ n → Cfg Δ m → Set where
  step⟶c : ∀{n m m' gid}{cfg cfg' : Cfg Δ n}{g : Group Δ m}{g' : Group Δ m'}{E : CfgE Δ n gid} → 
    [ gid ] g ⟶g g' → 
    cfg ≡C E [ m , g ] → cfg' ≡C E [ m' , g' ] →
    cfg ⟶c cfg'
  spawng⟶c : ∀{n m gid}{cfg cfg' : Cfg Δ n}{E₁ : CfgE Δ n gid}{g g' : Group Δ m}{Γ τ}{e e' : Exp Δ Γ [] τ}{q ρ cs}{x : Fin m}{E₂ : GroupE Δ m x}{E₃ : E Δ Γ [] AR τ}{Λ φ}{fun : Fun Δ Λ φ}{args} → 
    (envF : EnvF Δ) → (p : spawng fun args redex) → 
    e ≡ E₃ [ spawng fun args ] → e' ≡ E₃ [ val (A (AR n 0)) ] → 
    g ≡G E₂ [ ⟨ q , e , ρ , cs ⟩ ] → g' ≡G E₂ [ ⟨ q , e' , ρ , cs ⟩ ] → 
    cfg ≡C E₁ [ m , g ] → cfg' ≡C E₁ [ m , g' ] → 
    cfg ⟶c (suc zero , group (just zero) Data.Vec.[ ⟨ [] , lkp-fun envF fun , spawng-args-to-state fun args p , [] ⟩ ]) ∷ cfg'
  send-global⟶c : ∀{n m gid}{cfg cfg' : Cfg Δ n}{E₁ : CfgE Δ n gid}{g g' : Group Δ m}{Γ φ τ}{e e' : Exp Δ Γ [] τ}{q ρ cs}{x : Fin m}{E₂ : GroupE Δ m x}{E₃ : E Δ Γ [] φ τ}{msg : Val φ}{grp task} → 
    e ≡ E₃ [ send (val (A (AR grp task))) (val msg) ] → e' ≡ E₃ [ val msg ] → 
    g ≡G E₂ [ ⟨ q , e , ρ , cs ⟩ ] → g' ≡G E₂ [ ⟨ q , e' , ρ , cs ⟩ ] → 
    cfg ≡C E₁ [ m , g ] → cfg' ≡C E₁ [ m , g' ] → 
    cfg ⟶c cfg'

{-
wk-var : ∀{τ} → (Γ Σ : Ctx) (σ : Type) → Var (Γ ++ Σ) τ → Var (Γ ++ (σ ∷ Σ)) τ
wk-var [] [] σ ()
wk-var {τ} (.τ ∷ Γ) [] σ (z .τ) = z _
wk-var (x ∷ Γ) [] σ (s v) = s (wk-var Γ [] σ v)
wk-var {τ} [] (.τ ∷ Σ) σ (z .τ) = s (z _)
wk-var [] (x ∷ Σ) σ (s v) = s (s v)
wk-var {τ} (.τ ∷ Γ) (x₁ ∷ Σ) σ (z .τ) = z _
wk-var (x ∷ Γ) (x₁ ∷ Σ) σ (s v) = s (wk-var Γ (x₁ ∷ Σ) σ v)

wk' : ∀{Ξ Δ τ} → (Γ Σ : Ctx) → (σ : Type) → Exp Δ (Γ ++ Σ) Ξ τ → Exp Δ (Γ ++ (σ ∷ Σ)) Ξ τ

wk-explist : ∀{Δ Λ Ξ} → (Γ Σ : Ctx) → (σ : Type) → ExpList Δ (Γ ++ Σ) Ξ Λ → ExpList Δ (Γ ++ σ ∷ Σ) Ξ Λ
wk-explist Γ Σ σ [] = []
wk-explist Γ Σ σ (x ∷ el) = wk' Γ Σ σ x ∷ wk-explist Γ Σ σ el

wk' Γ Σ σ (var x) = var (wk-var Γ Σ σ x)
wk' Γ Σ σ (val x) = val x
wk' Γ Σ σ (e ≐ e₁) = wk' Γ Σ σ e ≐ wk' Γ Σ σ e₁
wk' Γ Σ σ (¬ e) = ¬ wk' Γ Σ σ e
wk' Γ Σ σ (e ∔ e₁) = wk' Γ Σ σ e ∔ wk' Γ Σ σ e₁
wk' Γ Σ σ (e ⊻ e₁) = wk' Γ Σ σ e ⊻ wk' Γ Σ σ e₁
wk' Γ Σ σ avail = avail
wk' Γ Σ σ (f （ args ）) = f （ wk-explist Γ Σ σ args ）
wk' Γ Σ σ (spawn f args) = spawn f (wk-explist Γ Σ σ args)
wk' Γ Σ σ (spawng f args) = spawng f (wk-explist Γ Σ σ args)
wk' Γ Σ σ yield = yield
wk' Γ Σ σ (x ≔ e) = wk-var Γ Σ σ x ≔ wk' Γ Σ σ e
wk' Γ Σ σ skip = skip
wk' Γ Σ σ (e , e₁) = wk' Γ Σ σ e , wk' Γ Σ σ e₁
wk' Γ Σ σ (If e then e₁ else e₂) = If wk' Γ Σ σ e then wk' Γ Σ σ e₁ else wk' Γ Σ σ e₂
wk' Γ Σ σ (While e do e₁) = While wk' Γ Σ σ e do wk' Γ Σ σ e₁
wk' Γ Σ σ (send e e₁) = send (wk' Γ Σ σ e) (wk' Γ Σ σ e₁)
wk' Γ Σ σ (receive e e₁ e₂ e₃) = receive (wk' (Un ∷ Γ) Σ σ e) (wk' (AR ∷ Γ) Σ σ e₁) (wk' (In ∷ Γ) Σ σ e₂) (wk' (Bo ∷ Γ) Σ σ e₃)
wk' Γ Σ σ (ignore e) = ignore (wk' Γ Σ σ e)

subst : ∀{Γ Δ Σ σ τ} → Var (Γ ++ (σ ∷ Σ)) σ → Val σ → Exp Δ (Γ ++ (σ ∷ Σ)) τ → Exp Δ (Γ ++ Σ) τ
subst x v e = {!!}
{-
data Eff : Set where
  none : Eff
  spawn : ∀{Γ Δ τ} → Fun Δ Γ τ → State Γ → Eff
  spawng : ∀{Γ Δ τ} → Fun Δ Γ τ → State Γ → Eff
  send : ∀{τ} → ARef → Val τ → Eff
  yield : Eff
-}


data GroupE (Δ : FCtx) : (n : ℕ) → Fin n → Set where
    task-E : ∀{n} → Vec (Task Δ) n → GroupE Δ (suc n) zero
    tasks-E : ∀{n m} → Task Δ → GroupE Δ n m → GroupE Δ (suc n) (suc m)

--                                                              ≡              [       ,           ,         ,              ]
data _≡G_[_,_,_,_] {Δ : FCtx} : ∀{Γ Ξ τ n}{m : Fin n} → Group Δ n → GroupE Δ n m → Queue → Exp Δ Γ Ξ τ → State Γ → List (Call Δ) → Set where
    task-≡G : ∀{Γ Ξ q τ ρ cs n}{e₀ : Exp Δ Γ Ξ τ}{tasks : Vec (Task Δ) n} → 
        group (just zero) (⟨ q , e₀ , ρ , cs ⟩ ∷ tasks) ≡G task-E tasks [ q  , e₀ , ρ , cs ]
    tasks-≡G : ∀{Γ Ξ q τ ρ cs m task}{e : Exp Δ Γ Ξ τ}{tasks : Vec (Task Δ) m}{n : Fin m}{E : GroupE Δ m n} → 
        group (just n) tasks ≡G E [ q , e , ρ , cs ] →
        group (just (suc n)) (task ∷ tasks) ≡G tasks-E task E [ q , e , ρ , cs ]
--    scheduler-≡G : ∀{Γ q τ ρ cs m}{tasks : Vec (Task Δ) m}{e : Exp Δ Γ Ξ τ} → 
--        (p : (∃₂ λ (n : Fin m) (E : GroupE Δ m n) → group (just n) tasks ≡G E [ q , e , ρ , cs ])) →
--        group nothing tasks ≡G proj₁ (proj₂ p) [ q , e , ρ , cs ]

data CfgE (Δ : FCtx) : ℕ → Set where
    head-E : ∀{n m}{m' : Fin m} → GroupE Δ m m' → Cfg Δ n → CfgE Δ (suc n)
    tail-E : ∀{n} → (∃ λ m → Group Δ m) → CfgE Δ n → CfgE Δ (suc n)

data _≡C_[_,_,_,_] {Δ} : ∀{Γ Ξ τ n} → Cfg Δ n → CfgE Δ n → Queue → Exp Δ Γ Ξ τ → State Γ → List (Call Δ) → Set where
    group-≡C : ∀{Γ Ξ q τ ρ cs m n}{e : Exp Δ Γ Ξ τ}{group : Group Δ m}{groups : Cfg Δ n}{m' : Fin m}{E : GroupE Δ m m'} → 
        group ≡G E [ q , e , ρ , cs ] → 
        ((m , group) ∷ groups) ≡C head-E E groups [ q , e , ρ , cs ]
    cfg-≡C : ∀{Γ Ξ q τ ρ cs n}{e : Exp Δ Γ Ξ τ}{group groups}{E : CfgE Δ n} → 
        groups ≡C E [ q , e , ρ , cs ] → 
        (group ∷ groups) ≡C tail-E group E [ q , e , ρ , cs ]

data _⟶_ {Δ} {envF : EnvF Δ} : ∀{n n'} → Cfg Δ n → Cfg Δ n' → Set where
    hole⟶ : ∀{Γ Ξ φ τ n cfg cfg' q ρ cs}{e₀ e₀' : Exp Δ Γ Ξ τ}{e e' : Exp Δ Γ Ξ φ}{E : E Δ Γ Ξ φ τ}{Ec : CfgE Δ n} → 
        q , e , ρ ↦ e' → 
        e₀ ≡ E [ e ] → e₀' ≡ E [ e' ] → 
        cfg ≡C Ec [ q , e₀ , ρ , cs ] → cfg' ≡C Ec [ q , e₀' , ρ , cs ] →
        cfg ⟶ cfg'
    ≔⟶ : ∀{Γ Ξ φ τ n q ρ cs cfg cfg'}{e e' : Exp Δ Γ Ξ τ}{E : E Δ Γ Ξ Un τ}{Ec : CfgE Δ n}{x : Var Γ φ}{v : Val φ} → 
        e ≡ E [ x ≔ val v ] → e' ≡ E [ skip ] →
        cfg ≡C Ec [ q , e , ρ , cs ] → cfg' ≡C Ec [ q , e' , upd x v ρ , cs ] →
        cfg ⟶ cfg'
    call⟶ : ∀{Γ Λ Ξ φ τ n q ρ cs cfg cfg'}{e : Exp Δ Γ Ξ τ}{f : Fun Δ Λ φ}{args : ExpList Δ Γ Ξ Λ}{Ec : CfgE Δ n}{E : E Δ Γ Ξ φ τ} → 
        e ≡ E [ f （ args ） ] → (r : (f （ args ）) redex) → 
        cfg ≡C Ec [ q , e , ρ , cs ] → cfg' ≡C Ec [ q , lkp-fun envF f , args-to-state f args r , < E / ρ > ∷ cs ] →
        cfg ⟶ cfg'
    spawn⟶ : ∀{Γ Λ Ξ φ τ n cfg q ρ cs cfg'}{e : Exp Δ Γ Ξ τ}{f : Fun Δ Λ φ}{args : ExpList Δ Γ Ξ Λ}{Ec : CfgE Δ n}{E : E Δ Γ Ξ AR τ} →
        e ≡ E [ spawn f args ] → (p : spawn f args redex) → 
        cfg ≡C Ec [ q , e , ρ , cs ] → cfg' ≡C Ec [ q , val (A (AR n {!!})) , ρ , cs ] →
        cfg ⟶ cfg'
-}      
{-
data GroupE (Δ : FCtx) : Ctx → Type → (n : ℕ) → Fin n → Set where
  task-E : ∀{Γ φ τ n} → Queue → E Δ Γ Ξ φ τ → State Γ → List (Call Δ) → Vec (Task Δ) n → GroupE Δ Γ Ξ φ (suc n) zero
  tasks-E : ∀{Γ φ n m} → Task Δ → GroupE Δ Γ Ξ φ n m → GroupE Δ Γ Ξ φ (suc n) (suc m)
--  nothing-E : ∀{Γ τ n} → Fin n → GroupE Δ Γ Ξ τ {!!} {!!} → GroupE Δ Γ Ξ τ {!!} {!!}

data _≡G_[_] {Δ : FCtx} : ∀{Γ φ}{n : ℕ}{m : Fin n} → Group Δ n → GroupE Δ Γ Ξ φ n m → Exp Δ Γ Ξ φ → Set where
   task-≡G : ∀{n Γ φ τ q ρ cs}{tasks  : Vec (Task Δ) n}{e₀ : Exp Δ Γ Ξ τ}{e : Exp Δ Γ Ξ φ}{E : E Δ Γ Ξ φ τ} → 
     e₀ ≡ E [ e ] → 
     group (just zero) (⟨ q , e₀ , ρ , cs ⟩ ∷ tasks) ≡G task-E q E ρ cs tasks [ e ]
   tasks-≡G : ∀{m Γ φ task}{tasks : Vec (Task Δ) m}{e : Exp Δ Γ Ξ φ}{n : Fin m}{E : GroupE Δ Γ Ξ φ m n} →
     group (just n) tasks ≡G E [ e ] → 
     group (just (suc n)) (task ∷ tasks) ≡G tasks-E task E [ e ]
   scheduler-≡G : ∀{Γ φ m}{tasks : Vec (Task Δ) m}{e : Exp Δ Γ Ξ φ}{n : Fin m} →
     (p : (∃ λ (E : GroupE Δ Γ Ξ φ m n) → (group (just n) tasks) ≡G E [ e ])) →
     group nothing tasks ≡G proj₁ p [ e ]

data CfgE (Δ : FCtx) : Ctx → Type → Set where
   head-E : ∀{Γ τ n m}{m' : Fin m} → GroupE Δ Γ Ξ τ m m' → Cfg Δ n → CfgE Δ Γ Ξ τ
   tail-E : ∀{Γ τ} → (∃ λ n → Group Δ n) → CfgE Δ Γ Ξ τ → CfgE Δ Γ Ξ τ

data _≡C_[_] {Δ} : ∀{n Γ φ} → Cfg Δ n → CfgE Δ Γ Ξ φ → Exp Δ Γ Ξ φ → Set where
  grp-≡C : ∀{Γ n m τ}{group : Group Δ m}{m' : Fin m}{groups : Cfg Δ n}{E : GroupE Δ Γ Ξ τ m m'}{e : Exp Δ Γ Ξ τ} →
   group ≡G E [ ? ] →
   ((m , group) ∷ groups) ≡C head-E E groups [ e ]
  cfg-≡C : ∀{Γ n τ group}{groups : Cfg Δ n}{E : CfgE Δ Γ Ξ τ}{e : Exp Δ Γ Ξ τ} →
   groups ≡C E [ e ] → 
   (group ∷ groups) ≡C tail-E group E [ e ]

data _⟶_ {Δ} : ∀{n m} → Cfg Δ n → Cfg Δ m → Set where
  hole⟶ : ∀{Γ n m τ}{cfg : Cfg Δ n}{cfg' : Cfg Δ m}{E : CfgE Δ Γ Ξ τ}{e e' : Exp Δ Γ Ξ τ} →
     cfg ≡C E [ e ] → cfg' ≡C E [ e' ] →
     {!!} , e , {!!} ↦ e' → 
     cfg ⟶ cfg'
-}
{-
-- identifiers : current group id, current task id, next group id, next task id (within my group)
data [_,_,_,_]_⟶_,_ {Δ} (myg : GroupID) (myt : TaskID) (nextg : GroupID) (nextt : TaskID) : Task Δ → Task Δ → Eff → Set where
 hole : ∀{q ts A B Γ}{ρ : State Γ} {e e' : Exp Δ Γ Ξ B} {E : E Δ Γ Ξ A B} {e₀ e₀' : Exp Δ Γ Ξ A} → 
     e ≡ E [ e₀ ] → q , e₀ , ρ ↦ e₀' → e' ≡ E [ e₀' ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , none
 ≔⟶ : ∀{q ts B τ Γ} {x : Var Γ τ} {e e' : Exp Δ Γ Ξ B} {E : E Δ Γ Ξ Un B} {v : Val τ} {ρ : State Γ} → 
     e ≡ E [ x ≔ val v ] → e' ≡ E [ skip ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , upd x v ρ , ts ⟩ , none
 call⟶ : ∀ {q ts A τ Γ Γ'} {f : Fun Δ Γ' τ} {args : ExpList Δ Γ Ξ Γ'} {E : E Δ Γ Ξ τ A} {e : Exp Δ Γ Ξ A} {ρ : State Γ} →
     (envF : EnvF Δ) → (z : e ≡ E [ f （ args ） ]) → (r : (f （ args ）) redex) → 
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , lkp-fun envF f , args-to-state f args r , < E / ρ > ∷ ts ⟩ , none
 spawn⟶ : ∀{Γ q ρ ts φ Γ' τ}{fun : Fun Δ Γ' τ}{args : ExpList Δ Γ Ξ Γ'}{e e' : Exp Δ Γ Ξ φ}{E : E Δ Γ Ξ AR φ} →
     e ≡ E [ spawn fun args ] → (p : spawn fun args redex) → e' ≡ E [ val (A (AR myg nextt)) ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , spawn fun (spawn-args-to-state fun args p)
 spawng⟶ : ∀{Γ q ρ ts φ Γ' τ}{fun : Fun Δ Γ' τ}{args : ExpList Δ Γ Ξ Γ'}{e e' : Exp Δ Γ Ξ φ}{E : E Δ Γ Ξ AR φ} →
     e ≡ E [ spawng fun args ] → (p : spawng fun args redex) → e' ≡ E [ val (A (AR nextg zero)) ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , spawng fun (spawng-args-to-state fun args p)
 yield⟶ : ∀{Γ q ρ ts A}{e e' : Exp Δ Γ Ξ A}{E : E Δ Γ Ξ Un A} →
     e ≡ E [ yield ] → e' ≡ E [ skip ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , yield
 send⟶  : ∀{Γ q ρ ts φ τ}{e e' : Exp Δ Γ Ξ τ}{E : E Δ Γ Ξ φ τ}{a : ARef}{v : Val φ} → 
     e ≡ E [ send (val (A a)) (val v) ] → e' ≡ E [ val v ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , send a v
 receive⟶Un : ∀{Γ τ φ E q ρ ts}{e e' : Exp Δ Γ Ξ τ}{e₁ : Exp Δ (Un ∷ Γ) φ}{e₂ : Exp Δ (AR ∷ Γ) φ}{e₃ : Exp Δ (In ∷ Γ) φ}{e₄ : Exp Δ (Bo ∷ Γ) φ} → 
     e ≡ E [ receive e₁ e₂ e₃ e₄ ] → e' ≡ E [ Let (val U) e₁ ] → 
     [ myg , myt , nextg , nextt ] ⟨ ((Un , U) ∷ q) , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , none
 receive⟶AR : ∀{Γ τ φ E q ρ ts}{e e' : Exp Δ Γ Ξ τ}{e₁ : Exp Δ (Un ∷ Γ) φ}{e₂ : Exp Δ (AR ∷ Γ) φ}{e₃ : Exp Δ (In ∷ Γ) φ}{e₄ : Exp Δ (Bo ∷ Γ) φ}{v : Val AR} → 
     e ≡ E [ receive e₁ e₂ e₃ e₄ ] → e' ≡ E [ Let (val v) e₂ ] → 
     [ myg , myt , nextg , nextt ] ⟨ ((AR , v) ∷ q) , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , none
-}
{-
infixr 4 _⇒_ 

data _⇒_ {Δ}{envF : EnvF Δ} : ∀{n} → Group envF n → (∃ λ n' → Group envF n') → Set where
  idle⇒ : ∀{n} → (tsk : Vec (Task Δ) n) → (x : Fin n) →
     group nothing tsk ⇒ n , group (just x) tsk

  step⇒ : ∀{n} → group (just n) tsks ⇒ group (just n) tsks' → 
     group (just (suc n)) (tsk ∷ tsks) ⇒ group (just (suc n)) (tsk ∷ tsks')

  step-yield⇒ : group (just n) tsks ⇒ group nothing tsks' → 
     group (just (suc n)) (tsk ∷ tsks) ⇒ group nothing (tsk ∷ tsks')
-}
--  yield⇒ : task ⟶ task' , yield →
--     group n tsk ⇒ group nothing tsk

--infixr 4 _⇒_ 

--data _⇒_ {m c c'} {Δ : FCtx m} {envF : EnvF Δ} : Cfg envF c → Cfg envF c' → Set where
-- mid : {task : Task Δ}{tasks tasks' : Cfg envF} → 
--     _⇒_ {_} {_} {envF} tasks tasks' →
--     (task ∷ tasks) ⇒ (task ∷ tasks')
-- step-task : ∀{task task' : Task Δ}{tasks : Cfg envF} → 
--     task ⟶ task' →
--     task ∷ tasks ⇒ task' ∷ tasks
-- async-call : 
