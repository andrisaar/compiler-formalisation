module Source where

open import Data.Bool
open import Data.Unit 
open import Data.List
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (_++_; group)
open import Data.Product
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

data Var : Ctx → Type → Set where
    z : ∀{Γ} → (τ : Type) → Var (τ ∷ Γ) τ
    s : ∀{τ σ Γ} → Var Γ τ → Var (σ ∷ Γ) τ

data Fun : FCtx → Ctx → Type → Set where
    z : ∀{Δ} → (Γ : Ctx) → (τ : Type) → Fun ((Γ , τ) ∷ Δ) Γ τ
    s : ∀{Γ Δ Λ σ τ} → Fun Δ Γ τ → Fun ((Λ , σ) ∷ Δ) Γ τ

mutual
  -- list of expressions
  data ExpList (Δ : FCtx) (Γ : Ctx) : Ctx → Set where
    [] : ExpList Δ Γ []
    _∷_ : ∀{τ T} → Exp Δ Γ τ → ExpList Δ Γ T → ExpList Δ Γ (τ ∷ T)

  data Exp (Δ : FCtx) (Γ : Ctx) : Type → Set where
    var   : ∀{τ} → Var Γ τ → Exp Δ Γ τ
    val   : ∀{τ} → Val τ → Exp Δ Γ τ
    _≐_   : ∀{τ} → Exp Δ Γ τ → Exp Δ Γ τ → Exp Δ Γ Bo
    ¬_    : Exp Δ Γ Bo → Exp Δ Γ Bo
    _∔_   : Exp Δ Γ In → Exp Δ Γ In → Exp Δ Γ In
    _⊻_   : Exp Δ Γ Bo → Exp Δ Γ Bo → Exp Δ Γ Bo
    avail : Exp Δ Γ Bo
    _（_） : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Λ → Exp Δ Γ τ
    spawn : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Λ → Exp Δ Γ AR
    spawng : ∀{Λ τ} → Fun Δ Λ τ → ExpList Δ Γ Λ → Exp Δ Γ AR
    yield : Exp Δ Γ Un

-- former statements
    _≔_           : ∀{τ} → Var Γ τ → Exp Δ Γ τ → Exp Δ Γ Un
    skip          : Exp Δ Γ Un
    _,_           : ∀{τ} → Exp Δ Γ Un → Exp Δ Γ τ → Exp Δ Γ τ
    If_then_else_ : ∀{τ} → Exp Δ Γ Bo → Exp Δ Γ τ → Exp Δ Γ τ → Exp Δ Γ τ
    While_do_     : Exp Δ Γ Bo → Exp Δ Γ Un → Exp Δ Γ Un -- TODO generalize it to τ, not just unit
    send          : ∀{τ} → Exp Δ Γ AR → Exp Δ Γ τ → Exp Δ Γ τ
-- TODO substitution of received messages
    receive       : ∀{τ} → Exp Δ (Un ∷ Γ) τ → Exp Δ (AR ∷ Γ) τ → Exp Δ (In ∷ Γ) τ → Exp Δ (Bo ∷ Γ) τ → Exp Δ Γ τ
    ignore        : ∀{τ} → Exp Δ Γ τ → Exp Δ Γ Un

data _values {Γ Δ} : ∀{Λ} → ExpList Γ Δ Λ → Set where
  []-values : [] values
  ∷-values  : ∀{τ T} → (v : Val τ) → (l : ExpList Γ Δ T) → l values → ((val v) ∷ l) values

data _redex {Γ Δ} : ∀{τ} → Exp Δ Γ τ → Set where
  var-redex     : ∀{τ}{v : Var Γ τ} → (var v) redex
  =-redex       : ∀{τ}{v₁ v₂ : Val τ} → ((val v₁) ≐ (val v₂)) redex
  +-redex       : ∀{v₁ v₂} → (val v₁ ∔ val v₂) redex
  ∨-redex       : ∀{v₁ v₂} → (val v₁ ⊻ val v₂) redex
  ¬-redex       : ∀{v} → (¬ val v) redex
  avail-redex   : avail redex
  ≔-redex       : ∀{τ v}{x : Var Γ τ} → (x ≔ val v) redex
  skip-redex    : skip redex
  ,-redex       : ∀{τ}{e : Exp Δ Γ τ} → (val U , e) redex
  ignore-redex  : ∀{τ}{v : Val τ} → ignore (val v) redex
  if-redex      : ∀{τ v}{e₁ e₂ : Exp Δ Γ τ} → (If (val v) then e₁ else e₂) redex
  while-redex   : ∀{e₀}{e : Exp Δ Γ Un} → (While e₀ do e) redex
  send-redex    : ∀{τ v₁}{v₂ : Val τ} → send (val v₁) (val v₂) redex
  receive-redex : ∀{τ}{e₁ : Exp Δ (Un ∷ Γ) τ}{e₂ : Exp Δ (AR ∷ Γ) τ}{e₃ : Exp Δ (In ∷ Γ) τ}{e₄ : Exp Δ (Bo ∷ Γ) τ} → receive e₁ e₂ e₃ e₄ redex
  call-redex    : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (fun （ args ）) redex
  spawn-redex   : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (spawn fun args) redex
  spawng-redex  : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (spawng fun args) redex
  yield-redex   : yield redex


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

  data FunE (Δ : FCtx) (Γ : Ctx) : Ctx → Set where
    empty : FunE Δ Γ []
    val : ∀{φ Φ} → Val φ → FunE Δ Γ Φ → FunE Δ Γ (φ ∷ Φ)
    exp : ∀{τ φ Φ} → E Δ Γ τ φ → ExpList Δ Γ Φ → FunE Δ Γ (φ ∷ Φ)

  -- Eval ctx : variable context, var ctx that goes in the hole, function context, type expected in the hole, return type
  data E (Δ : FCtx)(Γ : Ctx) : Type → Type → Set where
    □  : ∀{τ} → E Δ Γ τ τ
    ¬-E : ∀{τ} → E Δ Γ τ Bo → E Δ Γ τ Bo                              -- ¬ E
    ∨l-E : ∀{τ} → E Δ Γ τ Bo → Exp Δ Γ Bo → E Δ Γ τ Bo                 -- E ∨ e  
    ∨r-E : ∀{τ} → Val Bo → E Δ Γ τ Bo → E Δ Γ τ Bo -- v ∨ E            -- what about true ∨ E ?
    =l-E : ∀{A B} → E Δ Γ A B → Exp Δ Γ B → E Δ Γ A Bo                 -- E = e
    =r-E : ∀{A B} → Val B → E Δ Γ A B → E Δ Γ A Bo -- v = E
    +l-E : ∀{A} → E Δ Γ A In → Exp Δ Γ In → E Δ Γ A In                 -- E + e  
    +r-E : ∀{A} → Val In → E Δ Γ A In → E Δ Γ A In -- v + E
    
    call-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Λ → E Δ Γ A τ
    spawn-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Λ → E Δ Γ A AR
    spawng-E : ∀{A τ Λ} → (f : Fun Δ Λ τ) → FunE Δ Γ Λ → E Δ Γ A AR

    ≔-E : ∀{A τ} → (v : Var Γ τ) → E Δ Γ A τ → E Δ Γ A Un      -- x ≔ E
    ,-E : ∀{A B} → E Δ Γ A Un → Exp Δ Γ B → E Δ Γ A B                 -- E , e
    if-E : ∀{A B} → E Δ Γ A Bo → Exp Δ Γ B → Exp Δ Γ B → E Δ Γ A B     -- If E then e else e
    ignore-E : ∀{A B} → E Δ Γ A B → E Δ Γ A Un -- ignore E
    sendl-E : ∀{A B} → E Δ Γ A AR → Exp Δ Γ B → E Δ Γ A B                 -- send E e
    sendr-E : ∀{A B} → Val AR → E Δ Γ A B → E Δ Γ A B -- send v E
    letl-E : ∀{A σ τ} → E Δ Γ A σ → Exp Δ (σ ∷ Γ) τ → E Δ Γ A τ -- let E e
    letr-E : ∀{A σ τ} → Val σ → E Δ (σ ∷ Γ) A τ → E Δ Γ A τ -- let v E

infix 4 _≡_[_]
infix 4 _≡′_[_]

mutual
  data _≡′_[_] {Γ Δ} : ∀{φ ctx} → ExpList Δ Γ ctx → FunE Δ Γ ctx → Exp Δ Γ φ → Set where
    exp-≡′ : ∀{ctx φ}{e' : Exp Δ Γ φ}{τ}{E : E Δ Γ φ τ}{e}{l : ExpList Δ Γ ctx} → 
         e ≡ E [ e' ] → 
         e ∷ l ≡′ exp E l [ e' ]
    val-≡′ : ∀{ctx l}{E : FunE Δ Γ ctx}{τ}{υ : Val τ}{φ}{e : Exp Δ Γ φ} → 
         l ≡′ E [ e ] → 
         (val υ) ∷ l ≡′ val υ E [ e ]

  data _≡_[_] {Γ Δ} : ∀{τ φ} → Exp Δ Γ τ → E Δ Γ φ τ → Exp Δ Γ φ → Set where
    exp-≡ : ∀{τ} {e : Exp Δ Γ τ} → -- e redex →
      e ≡ □ [ e ]
    =l-≡ : ∀{τ φ E} {e₀ e₁ : Exp Δ Γ τ} {e : Exp Δ Γ φ} → e₀ ≡ E [ e ] → 
      e₀ ≐ e₁ ≡ =l-E E e₁ [ e ]
    =r-≡ : ∀{A B E} {e₀ : Val A} {e₁ : Exp Δ Γ A} {e : Exp Δ Γ B} → e₁ ≡ E [ e ] → 
      val e₀ ≐ e₁ ≡ =r-E e₀ E [ e ]
    ¬-≡ : ∀{B E} {e₀ : Exp Δ Γ Bo}{e : Exp Δ Γ B} → e₀ ≡ E [ e ] → 
      ¬ e₀ ≡ ¬-E E [ e ]
    +l-≡ : ∀{B E} {e₀ e₁ : Exp Δ Γ In} {e : Exp Δ Γ B} → e₀ ≡ E [ e ] → 
      e₀ ∔ e₁ ≡ +l-E E e₁ [ e ]
    +r-≡ : ∀{B E} {e₀ : Val In} {e₁ : Exp Δ Γ In} {e : Exp Δ Γ B} → e₁ ≡ E [ e ] → 
      val e₀ ∔ e₁ ≡ +r-E e₀ E [ e ]
    ∨l-≡ : ∀{B E} {e₀ e₁ : Exp Δ Γ Bo} {e : Exp Δ Γ B} → e₀ ≡ E [ e ] → 
      e₀ ⊻ e₁ ≡ ∨l-E E e₁ [ e ]
    ∨r-≡ : ∀{B E} {e₀ : Val Bo} {e₁ : Exp Δ Γ Bo} {e : Exp Δ Γ B} → e₁ ≡ E [ e ] → 
      val e₀ ⊻ e₁ ≡ ∨r-E e₀ E [ e ]
    ≔-≡ : ∀{τ φ} {x : Var Γ φ} {e₀ : Exp Δ Γ φ}{e : Exp Δ Γ τ} {E : E Δ Γ τ φ} → e₀ ≡ E [ e ] → 
      x ≔ e₀ ≡ ≔-E x E [ e ]
    if-≡ : ∀{A B E e₀} {e₁ e₂ : Exp Δ Γ A} {e : Exp Δ Γ B} → e₀ ≡ E [ e ] → 
      If e₀ then e₁ else e₂ ≡ if-E E e₁ e₂ [ e ]
    ignore-≡ : ∀{A B E} {e₀ : Exp Δ Γ A}{e : Exp Δ Γ B} → e₀ ≡ E [ e ] → 
      ignore e₀ ≡ ignore-E E [ e ]
    sendl-≡ : ∀{A B E e₁} {e₂ : Exp Δ Γ B}{e : Exp Δ Γ A} → e₁ ≡ E [ e ] →
      send e₁ e₂ ≡ sendl-E E e₂ [ e ]
    sendr-≡ : ∀{A B E v₁} {e₂ : Exp Δ Γ B} {e : Exp Δ Γ A} → e₂ ≡ E [ e ] → 
      send (val v₁) e₂ ≡ sendr-E v₁ E [ e ]
    call-≡ : ∀{τ φ}{e : Exp Δ Γ τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      fun （ args ） ≡ call-E fun E [ e ]
    spawn-≡ : ∀{τ φ}{e : Exp Δ Γ τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawn fun args ≡ spawn-E fun E [ e ]
    spawng-≡ : ∀{τ φ}{e : Exp Δ Γ τ}{Γ'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawng fun args ≡ spawng-E fun E [ e ]
    ,-≡ : ∀{τ φ e₀}{e₁ : Exp Δ Γ τ}{E : E Δ Γ φ Un}{e : Exp Δ Γ φ} →  e₀ ≡ E [ e ] → 
      (e₀ , e₁) ≡ ,-E E e₁ [ e ]


data EnvF' (Δ : FCtx) : FCtx → Set where
 [] : EnvF' Δ []
 _∷_ : ∀{Γ φ Φ} → Exp Δ Γ φ → EnvF' Δ Φ → EnvF' Δ ((Γ , φ) ∷ Φ)

EnvF : FCtx → Set
EnvF Δ = EnvF' Δ Δ

data Call (Δ : FCtx) : Set where
  <_/_> : ∀{φ τ Γ} → E Δ Γ φ τ → State Γ → Call Δ

data Task (Δ : FCtx) : Set where
  ⟨_,_,_,_⟩ : Queue → ∀{Γ τ} → Exp Δ Γ τ → State Γ → List (Call Δ) → Task Δ

data Group (Δ : FCtx) : ℕ → Set where
  group : ∀{n} → Maybe (Fin n) → Vec (Task Δ) n → Group Δ n

-- indexed by the number of groups
Cfg : FCtx → ℕ → Set
Cfg Δ n = Vec (∃ λ m → Group Δ m) n

lkp-fun : ∀{Δ Γ' Δ' τ} → EnvF' Δ' Δ → (f : Fun Δ Γ' τ) → Exp Δ' Γ' τ
lkp-fun []         ()
lkp-fun (f ∷ _)    (z ._ ._) = f
lkp-fun (_ ∷ envF) (s fun)   = lkp-fun envF fun

a2s' : ∀{Γ Δ Γ'} → (args : ExpList Γ Δ Γ') → args values → State Γ'
a2s' []          []-values = []
a2s' (._ ∷ args) (∷-values va ._ p) = va ∷ a2s' args p

args-to-state : ∀{τ Γ Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Λ) → fun （ args ） redex → State Λ
args-to-state fun args (call-redex x) = a2s' args x

spawn-args-to-state : ∀{τ Γ Δ Γ'} → (fun : Fun Δ Γ' τ) → (args : ExpList Δ Γ Γ') → spawn fun args redex → State Γ'
spawn-args-to-state fun args (spawn-redex x) = a2s' args x

spawng-args-to-state : ∀{τ Γ Δ Γ'} → (fun : Fun Δ Γ' τ) → (args : ExpList Δ Γ Γ') → spawng fun args redex → State Γ'
spawng-args-to-state fun args (spawng-redex x) = a2s' args x

wk-var : ∀{τ} → (Γ Σ : Ctx) (σ : Type) → Var (Γ ++ Σ) τ → Var (Γ ++ (σ ∷ Σ)) τ
wk-var [] [] σ ()
wk-var {τ} (.τ ∷ Γ) [] σ (z .τ) = z _
wk-var (x ∷ Γ) [] σ (s v) = s (wk-var Γ [] σ v)
wk-var {τ} [] (.τ ∷ Σ) σ (z .τ) = s (z _)
wk-var [] (x ∷ Σ) σ (s v) = s (s v)
wk-var {τ} (.τ ∷ Γ) (x₁ ∷ Σ) σ (z .τ) = z _
wk-var (x ∷ Γ) (x₁ ∷ Σ) σ (s v) = s (wk-var Γ (x₁ ∷ Σ) σ v)

wk' : ∀{Δ τ} → (Γ Σ : Ctx) → (σ : Type) → Exp Δ (Γ ++ Σ) τ → Exp Δ (Γ ++ (σ ∷ Σ)) τ

wk-explist : ∀{Δ Λ} → (Γ Σ : Ctx) → (σ : Type) → ExpList Δ (Γ ++ Σ) Λ → ExpList Δ (Γ ++ σ ∷ Σ) Λ
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

data _,_,_↦_ {Γ Δ} : ∀{τ} → Queue → Exp Δ Γ τ → State Γ → Exp Δ Γ τ → Set where
  var↦         : ∀{q τ ρ}{v : Var Γ τ} → q , var v                        , ρ ↦ val (lkp ρ v)
  ∔↦           : ∀{q v₁ v₂ ρ} →          q , (val (N v₁)) ∔ (val (N v₂)) , ρ ↦ val (N (v₁ + v₂))
  ⊻↦           : ∀{q v₁ v₂ ρ} →          q , (val (B v₁)) ⊻ (val (B v₂))  , ρ ↦ val (B (v₁ ∨ v₂))
  ¬↦           : ∀{q v ρ} →              q , ¬ (val (B v))                , ρ ↦ val (B (not v))
  avail↦-true  : ∀{m q ρ} →        (m ∷ q) , avail                        , ρ ↦ val (B true)
  avail↦-false : ∀{ρ} →                 [] , avail                        , ρ ↦ val (B false)
  ≐↦-int       : ∀{q v₁ v₂ ρ} →          q , (val (N v₁)) ≐ (val (N v₂))  , ρ ↦ val (B (v₁ ≡n v₂))
  ≐↦-bool      : ∀{q v₁ v₂ ρ} →          q , (val (B v₁)) ≐ (val (B v₂))  , ρ ↦ val (B (v₁ ≡b v₂))
-- some of stmts
  skip↦        : ∀{q ρ} →                        q , skip                               , ρ ↦ val U
  seq↦         : ∀{q ρ τ} {e : Exp Δ Γ τ} →      q , (val U , e)                        , ρ ↦ e
  IfT↦         : ∀ {q ρ τ} {e₁ e₂ : Exp Δ Γ τ} → q , If (val (B true)) then e₁ else e₂  , ρ ↦ e₁
  IfF↦         : ∀{q ρ τ} {e₁ e₂ : Exp Δ Γ τ} →  q , If (val (B false)) then e₁ else e₂ , ρ ↦ e₂
  While↦       : ∀{q e' e ρ} →                   q , While e do e'                      , ρ ↦ If e then (e' , While e do e') else skip
  ignore↦      : ∀{q τ ρ}{v : Val τ} →           q , ignore (val v)                     , ρ ↦ val U

data GroupE (Δ : FCtx) : (n : ℕ) → Fin n → Set where
    task-E : ∀{n} → Vec (Task Δ) n → GroupE Δ (suc n) zero
    tasks-E : ∀{n m} → Task Δ → GroupE Δ n m → GroupE Δ (suc n) (suc m)

--                                                              ≡              [       ,           ,         ,              ]
data _≡G_[_,_,_,_] {Δ : FCtx} : ∀{Γ τ n}{m : Fin n} → Group Δ n → GroupE Δ n m → Queue → Exp Δ Γ τ → State Γ → List (Call Δ) → Set where
    task-≡G : ∀{Γ q τ ρ cs n}{e₀ : Exp Δ Γ τ}{tasks : Vec (Task Δ) n} → 
        group (just zero) (⟨ q , e₀ , ρ , cs ⟩ ∷ tasks) ≡G task-E tasks [ q  , e₀ , ρ , cs ]
    tasks-≡G : ∀{Γ q τ ρ cs m task}{e : Exp Δ Γ τ}{tasks : Vec (Task Δ) m}{n : Fin m}{E : GroupE Δ m n} → 
        group (just n) tasks ≡G E [ q , e , ρ , cs ] →
        group (just (suc n)) (task ∷ tasks) ≡G tasks-E task E [ q , e , ρ , cs ]
--    scheduler-≡G : ∀{Γ q τ ρ cs m}{tasks : Vec (Task Δ) m}{e : Exp Δ Γ τ} → 
--        (p : (∃₂ λ (n : Fin m) (E : GroupE Δ m n) → group (just n) tasks ≡G E [ q , e , ρ , cs ])) →
--        group nothing tasks ≡G proj₁ (proj₂ p) [ q , e , ρ , cs ]

data CfgE (Δ : FCtx) : ℕ → Set where
    head-E : ∀{n m}{m' : Fin m} → GroupE Δ m m' → Cfg Δ n → CfgE Δ (suc n)
    tail-E : ∀{n} → (∃ λ m → Group Δ m) → CfgE Δ n → CfgE Δ (suc n)

data _≡C_[_,_,_,_] {Δ} : ∀{Γ τ n} → Cfg Δ n → CfgE Δ n → Queue → Exp Δ Γ τ → State Γ → List (Call Δ) → Set where
    group-≡C : ∀{Γ q τ ρ cs m n}{e : Exp Δ Γ τ}{group : Group Δ m}{groups : Cfg Δ n}{m' : Fin m}{E : GroupE Δ m m'} → 
        group ≡G E [ q , e , ρ , cs ] → 
        ((m , group) ∷ groups) ≡C head-E E groups [ q , e , ρ , cs ]
    cfg-≡C : ∀{Γ q τ ρ cs n}{e : Exp Δ Γ τ}{group groups}{E : CfgE Δ n} → 
        groups ≡C E [ q , e , ρ , cs ] → 
        (group ∷ groups) ≡C tail-E group E [ q , e , ρ , cs ]

data _⟶_ {Δ} {envF : EnvF Δ} : ∀{n n'} → Cfg Δ n → Cfg Δ n' → Set where
    hole⟶ : ∀{Γ φ τ n cfg cfg' q ρ cs}{e₀ e₀' : Exp Δ Γ τ}{e e' : Exp Δ Γ φ}{E : E Δ Γ φ τ}{Ec : CfgE Δ n} → 
        q , e , ρ ↦ e' → 
        e₀ ≡ E [ e ] → e₀' ≡ E [ e' ] → 
        cfg ≡C Ec [ q , e₀ , ρ , cs ] → cfg' ≡C Ec [ q , e₀' , ρ , cs ] →
        cfg ⟶ cfg'
    ≔⟶ : ∀{Γ φ τ n q ρ cs cfg cfg'}{e e' : Exp Δ Γ τ}{E : E Δ Γ Un τ}{Ec : CfgE Δ n}{x : Var Γ φ}{v : Val φ} → 
        e ≡ E [ x ≔ val v ] → e' ≡ E [ skip ] →
        cfg ≡C Ec [ q , e , ρ , cs ] → cfg' ≡C Ec [ q , e' , upd x v ρ , cs ] →
        cfg ⟶ cfg'
    call⟶ : ∀{Γ Λ φ τ n q ρ cs cfg cfg'}{e : Exp Δ Γ τ}{f : Fun Δ Λ φ}{args : ExpList Δ Γ Λ}{Ec : CfgE Δ n}{E : E Δ Γ φ τ} → 
        e ≡ E [ f （ args ） ] → (r : (f （ args ）) redex) → 
        cfg ≡C Ec [ q , e , ρ , cs ] → cfg' ≡C Ec [ q , lkp-fun envF f , args-to-state f args r , < E / ρ > ∷ cs ] →
        cfg ⟶ cfg'
    spawn⟶ : ∀{Γ Λ φ τ n cfg q ρ cs cfg'}{e : Exp Δ Γ τ}{f : Fun Δ Λ φ}{args : ExpList Δ Γ Λ}{Ec : CfgE Δ n}{E : E Δ Γ AR τ} →
        e ≡ E [ spawn f args ] → (p : spawn f args redex) → 
        cfg ≡C Ec [ q , e , ρ , cs ] → cfg' ≡C Ec [ q , val (A (AR n {!!})) , ρ , cs ] →
        cfg ⟶ cfg'
     
{-
data GroupE (Δ : FCtx) : Ctx → Type → (n : ℕ) → Fin n → Set where
  task-E : ∀{Γ φ τ n} → Queue → E Δ Γ φ τ → State Γ → List (Call Δ) → Vec (Task Δ) n → GroupE Δ Γ φ (suc n) zero
  tasks-E : ∀{Γ φ n m} → Task Δ → GroupE Δ Γ φ n m → GroupE Δ Γ φ (suc n) (suc m)
--  nothing-E : ∀{Γ τ n} → Fin n → GroupE Δ Γ τ {!!} {!!} → GroupE Δ Γ τ {!!} {!!}

data _≡G_[_] {Δ : FCtx} : ∀{Γ φ}{n : ℕ}{m : Fin n} → Group Δ n → GroupE Δ Γ φ n m → Exp Δ Γ φ → Set where
   task-≡G : ∀{n Γ φ τ q ρ cs}{tasks  : Vec (Task Δ) n}{e₀ : Exp Δ Γ τ}{e : Exp Δ Γ φ}{E : E Δ Γ φ τ} → 
     e₀ ≡ E [ e ] → 
     group (just zero) (⟨ q , e₀ , ρ , cs ⟩ ∷ tasks) ≡G task-E q E ρ cs tasks [ e ]
   tasks-≡G : ∀{m Γ φ task}{tasks : Vec (Task Δ) m}{e : Exp Δ Γ φ}{n : Fin m}{E : GroupE Δ Γ φ m n} →
     group (just n) tasks ≡G E [ e ] → 
     group (just (suc n)) (task ∷ tasks) ≡G tasks-E task E [ e ]
   scheduler-≡G : ∀{Γ φ m}{tasks : Vec (Task Δ) m}{e : Exp Δ Γ φ}{n : Fin m} →
     (p : (∃ λ (E : GroupE Δ Γ φ m n) → (group (just n) tasks) ≡G E [ e ])) →
     group nothing tasks ≡G proj₁ p [ e ]

data CfgE (Δ : FCtx) : Ctx → Type → Set where
   head-E : ∀{Γ τ n m}{m' : Fin m} → GroupE Δ Γ τ m m' → Cfg Δ n → CfgE Δ Γ τ
   tail-E : ∀{Γ τ} → (∃ λ n → Group Δ n) → CfgE Δ Γ τ → CfgE Δ Γ τ

data _≡C_[_] {Δ} : ∀{n Γ φ} → Cfg Δ n → CfgE Δ Γ φ → Exp Δ Γ φ → Set where
  grp-≡C : ∀{Γ n m τ}{group : Group Δ m}{m' : Fin m}{groups : Cfg Δ n}{E : GroupE Δ Γ τ m m'}{e : Exp Δ Γ τ} →
   group ≡G E [ ? ] →
   ((m , group) ∷ groups) ≡C head-E E groups [ e ]
  cfg-≡C : ∀{Γ n τ group}{groups : Cfg Δ n}{E : CfgE Δ Γ τ}{e : Exp Δ Γ τ} →
   groups ≡C E [ e ] → 
   (group ∷ groups) ≡C tail-E group E [ e ]

data _⟶_ {Δ} : ∀{n m} → Cfg Δ n → Cfg Δ m → Set where
  hole⟶ : ∀{Γ n m τ}{cfg : Cfg Δ n}{cfg' : Cfg Δ m}{E : CfgE Δ Γ τ}{e e' : Exp Δ Γ τ} →
     cfg ≡C E [ e ] → cfg' ≡C E [ e' ] →
     {!!} , e , {!!} ↦ e' → 
     cfg ⟶ cfg'
-}
{-
-- identifiers : current group id, current task id, next group id, next task id (within my group)
data [_,_,_,_]_⟶_,_ {Δ} (myg : GroupID) (myt : TaskID) (nextg : GroupID) (nextt : TaskID) : Task Δ → Task Δ → Eff → Set where
 hole : ∀{q ts A B Γ}{ρ : State Γ} {e e' : Exp Δ Γ B} {E : E Δ Γ A B} {e₀ e₀' : Exp Δ Γ A} → 
     e ≡ E [ e₀ ] → q , e₀ , ρ ↦ e₀' → e' ≡ E [ e₀' ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , none
 ≔⟶ : ∀{q ts B τ Γ} {x : Var Γ τ} {e e' : Exp Δ Γ B} {E : E Δ Γ Un B} {v : Val τ} {ρ : State Γ} → 
     e ≡ E [ x ≔ val v ] → e' ≡ E [ skip ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , upd x v ρ , ts ⟩ , none
 call⟶ : ∀ {q ts A τ Γ Γ'} {f : Fun Δ Γ' τ} {args : ExpList Δ Γ Γ'} {E : E Δ Γ τ A} {e : Exp Δ Γ A} {ρ : State Γ} →
     (envF : EnvF Δ) → (z : e ≡ E [ f （ args ） ]) → (r : (f （ args ）) redex) → 
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , lkp-fun envF f , args-to-state f args r , < E / ρ > ∷ ts ⟩ , none
 spawn⟶ : ∀{Γ q ρ ts φ Γ' τ}{fun : Fun Δ Γ' τ}{args : ExpList Δ Γ Γ'}{e e' : Exp Δ Γ φ}{E : E Δ Γ AR φ} →
     e ≡ E [ spawn fun args ] → (p : spawn fun args redex) → e' ≡ E [ val (A (AR myg nextt)) ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , spawn fun (spawn-args-to-state fun args p)
 spawng⟶ : ∀{Γ q ρ ts φ Γ' τ}{fun : Fun Δ Γ' τ}{args : ExpList Δ Γ Γ'}{e e' : Exp Δ Γ φ}{E : E Δ Γ AR φ} →
     e ≡ E [ spawng fun args ] → (p : spawng fun args redex) → e' ≡ E [ val (A (AR nextg zero)) ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , spawng fun (spawng-args-to-state fun args p)
 yield⟶ : ∀{Γ q ρ ts A}{e e' : Exp Δ Γ A}{E : E Δ Γ Un A} →
     e ≡ E [ yield ] → e' ≡ E [ skip ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , yield
 send⟶  : ∀{Γ q ρ ts φ τ}{e e' : Exp Δ Γ τ}{E : E Δ Γ φ τ}{a : ARef}{v : Val φ} → 
     e ≡ E [ send (val (A a)) (val v) ] → e' ≡ E [ val v ] →
     [ myg , myt , nextg , nextt ] ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , send a v
 receive⟶Un : ∀{Γ τ φ E q ρ ts}{e e' : Exp Δ Γ τ}{e₁ : Exp Δ (Un ∷ Γ) φ}{e₂ : Exp Δ (AR ∷ Γ) φ}{e₃ : Exp Δ (In ∷ Γ) φ}{e₄ : Exp Δ (Bo ∷ Γ) φ} → 
     e ≡ E [ receive e₁ e₂ e₃ e₄ ] → e' ≡ E [ Let (val U) e₁ ] → 
     [ myg , myt , nextg , nextt ] ⟨ ((Un , U) ∷ q) , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , none
 receive⟶AR : ∀{Γ τ φ E q ρ ts}{e e' : Exp Δ Γ τ}{e₁ : Exp Δ (Un ∷ Γ) φ}{e₂ : Exp Δ (AR ∷ Γ) φ}{e₃ : Exp Δ (In ∷ Γ) φ}{e₄ : Exp Δ (Bo ∷ Γ) φ}{v : Val AR} → 
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
