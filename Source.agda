-- {-# OPTIONS --type-in-type #-}
module Source where

open import Data.Bool
open import Data.Unit 
open import Data.List
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (group)
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
Ctx : ℕ → Set
Ctx n = Vec Type n

-- function contxt: maps functions to parameter types and return type
FCtx : ℕ → Set
FCtx m =  Vec ((∃ λ n → Ctx n) × Type) m

mutual
  -- list of expressions
  data ExpList {n m} (Γ : Ctx n)(Δ : FCtx m) : {n : ℕ} → Ctx n → Set where
    [] : ExpList Γ Δ []
    _∷_ : ∀{τ l}{T : Ctx l} → Exp Γ Δ τ → ExpList Γ Δ T → ExpList Γ Δ (τ ∷ T)

  data Val : Type → Set where
    U : Val Un
    A : ARef → Val AR
    N : ℕ → Val In
    B : Bool → Val Bo

  data Var : ∀{n} → Ctx n → Type → Set where
    z : ∀{n}{Γ : Ctx n} → (τ : Type) → Var (τ ∷ Γ) τ
    s : ∀{τ σ n}{Γ : Ctx n} → Var Γ τ → Var (σ ∷ Γ) τ

  data Fun : ∀{m n} → FCtx m → Ctx n → Type → Set where
    z : ∀{n}{Δ : FCtx n} → (Γ : Ctx n) → (τ : Type) → Fun (((n , Γ) , τ) ∷ Δ) Γ τ
    s : ∀{n n' m τ σ}{Γ : Ctx n}{Γ' : Ctx n'}{Δ : FCtx m} → Fun Δ Γ τ → Fun (((n' , Γ') , σ) ∷ Δ) Γ τ

  data Exp {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Set where
    var   : ∀{τ} → Var Γ τ → Exp Γ Δ τ
    val   : ∀{τ} → Val τ → Exp Γ Δ τ
    _≐_   : ∀{τ} → Exp Γ Δ τ → Exp Γ Δ τ → Exp Γ Δ Bo
    ¬_    : Exp Γ Δ Bo → Exp Γ Δ Bo
    _∔_   : Exp Γ Δ In → Exp Γ Δ In → Exp Γ Δ In
    _⊻_   : Exp Γ Δ Bo → Exp Γ Δ Bo → Exp Γ Δ Bo
    avail : Exp Γ Δ Bo
    _（_） : ∀{n' τ}{Γ' : Ctx n'} → Fun Δ Γ' τ → ExpList Γ Δ Γ' → Exp Γ Δ τ
    spawn : ∀{n' τ}{Γ' : Ctx n'} → Fun Δ Γ' τ → ExpList Γ Δ Γ' → Exp Γ Δ AR
    spawng : ∀{n' τ}{Γ' : Ctx n'} → Fun Δ Γ' τ → ExpList Γ Δ Γ' → Exp Γ Δ AR
    yield : Exp Γ Δ Un
-- former statements
    _≔_           : ∀{τ} → Var Γ τ → Exp Γ Δ τ → Exp Γ Δ Un
    skip          : Exp Γ Δ Un
    _,_           : ∀{τ} → Exp Γ Δ Un → Exp Γ Δ τ → Exp Γ Δ τ
    If_then_else_ : ∀{τ} → Exp Γ Δ Bo → Exp Γ Δ τ → Exp Γ Δ τ → Exp Γ Δ τ
    While_do_     : Exp Γ Δ Bo → Exp Γ Δ Un → Exp Γ Δ Un -- TODO generalize it to τ, not just unit
    send          : ∀{τ} → Exp Γ Δ AR → Exp Γ Δ τ → Exp Γ Δ τ
    receive       : ∀{τ} → Exp (Un ∷ Γ) Δ τ → Exp (AR ∷ Γ) Δ τ → Exp (In ∷ Γ) Δ τ → Exp (Bo ∷ Γ) Δ τ → Exp Γ Δ τ
    ignore        : ∀{τ} → Exp Γ Δ τ → Exp Γ Δ Un

data _values {n}{Γ : Ctx n}{m}{Δ : FCtx m} : ∀{n'}{Γ' : Ctx n'} → ExpList Γ Δ Γ' → Set where
  []-values : [] values
  ∷-values  : ∀{n' τ}{T : Ctx n'} → (v : Val τ) → (l : ExpList Γ Δ T) → l values → ((val v) ∷ l) values

data _redex {n m}{Γ : Ctx n}{Δ : FCtx m} : ∀{τ} → Exp Γ Δ τ → Set where
  var-redex     : ∀{τ}{v : Var Γ τ} → (var v) redex
  =-redex       : ∀{τ}{v₁ v₂ : Val τ} → ((val v₁) ≐ (val v₂)) redex
  +-redex       : ∀{v₁ v₂} → (val v₁ ∔ val v₂) redex
  ∨-redex       : ∀{v₁ v₂} → (val v₁ ⊻ val v₂) redex
  ¬-redex       : ∀{v} → (¬ val v) redex
  avail-redex   : avail redex
  ≔-redex       : ∀{τ}{x : Var Γ τ}{v} → (x ≔ val v) redex
  skip-redex    : skip redex
  ,-redex       : ∀{τ}{e : Exp Γ Δ τ} → (val U , e) redex
  ignore-redex  : ∀{τ}{v : Val τ} → ignore (val v) redex
  if-redex      : ∀{v τ} {e₁ e₂ : Exp Γ Δ τ} → (If (val v) then e₁ else e₂) redex
  while-redex   : ∀{e₀} {e : Exp Γ Δ Un} → (While e₀ do e) redex
  send-redex    : ∀{v₁ τ}{v₂ : Val τ} → send (val v₁) (val v₂) redex
  receive-redex : ∀{τ}{e₁ : Exp (Un ∷ Γ) Δ τ}{e₂ : Exp (AR ∷ Γ) Δ τ}{e₃ : Exp (In ∷ Γ) Δ τ}{e₄ : Exp (Bo ∷ Γ) Δ τ} → receive e₁ e₂ e₃ e₄ redex
  call-redex    : ∀{n' τ}{Γ' : Ctx n'}{fun : Fun Δ Γ' τ}{args} → args values → (fun （ args ）) redex
  spawn-redex   : ∀{n' τ}{Γ' : Ctx n'}{fun : Fun Δ Γ' τ}{args} → args values → (spawn fun args) redex
  spawng-redex  : ∀{n' τ}{Γ' : Ctx n'}{fun : Fun Δ Γ' τ}{args} → args values → (spawng fun args) redex
  yield-redex   : yield redex


data State : ∀{n} → Ctx n → Set where
  []  : State []
  _∷_ : ∀{τ n} {Γ : Ctx n} → Val τ → State Γ → State (τ ∷ Γ)

lkp : ∀{n τ} {Γ : Ctx n} → State Γ → (x : Var Γ τ) → Val τ
lkp []       ()
lkp (x ∷ _)  (z _) = x
lkp (_ ∷ st) (s x) = lkp st x

upd : ∀{n τ} {Γ : Ctx n} → Var Γ τ → Val τ → State Γ → State Γ
upd ()    _  []
upd (z _) va (_ ∷ st) = va ∷ st
upd (s x) va (v ∷ st) = v ∷ upd x va st

-- append messages to the end, pop them from the head
Queue : Set
Queue = List (∃ λ τ → Val τ)

data _,_,_↦_ {n m} {Γ : Ctx n} {Δ : FCtx m} : ∀{τ} → Queue → Exp Γ Δ τ → State Γ → Exp Γ Δ τ → Set where
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
  seq↦         : ∀{q ρ τ} {e : Exp Γ Δ τ} →      q , (val U , e)                        , ρ ↦ e
  IfT↦         : ∀ {q ρ τ} {e₁ e₂ : Exp Γ Δ τ} → q , If (val (B true)) then e₁ else e₂  , ρ ↦ e₁
  IfF↦         : ∀{q ρ τ} {e₁ e₂ : Exp Γ Δ τ} →  q , If (val (B false)) then e₁ else e₂ , ρ ↦ e₂
  While↦       : ∀{q e' e ρ} →                   q , While e do e'                      , ρ ↦ If e then (e' , While e do e') else skip
  ignore↦      : ∀{q τ ρ}{v : Val τ} →           q , ignore (val v)                     , ρ ↦ val U


-- evaluation ctx, indexed by the type of the hole and the return type
mutual

  data FunE {n m} (Γ : Ctx n) (Δ : FCtx m) : {n' : ℕ} → Vec Type n' → Set where
    empty : FunE Γ Δ []
    val : ∀{φ n'}{Φ : Vec Type n'} → Val φ → FunE Γ Δ Φ → FunE Γ Δ (φ ∷ Φ)
    exp : ∀{τ φ n'}{Φ : Vec Type n'} → E Γ Δ τ φ → ExpList Γ Δ Φ → FunE Γ Δ (φ ∷ Φ)

  -- Eval ctx : variable context, function context, type expected in the hole, return type
  data E {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Type → Set where
    □  : ∀{τ} → E Γ Δ τ τ
    ¬-E : ∀{τ} → E Γ Δ τ Bo → E Γ Δ τ Bo                              -- ¬ E
    ∨l-E : ∀{A} → E Γ Δ A Bo → Exp Γ Δ Bo → E Γ Δ A Bo                 -- E ∨ e  
    ∨r-E : ∀{A} → Val Bo → E Γ Δ A Bo → E Γ Δ A Bo -- v ∨ E            -- what about true ∨ E ?
    =l-E : ∀{A B} → E Γ Δ A B → Exp Γ Δ B → E Γ Δ A Bo                 -- E = e
    =r-E : ∀{A B} → Val B → E Γ Δ A B → E Γ Δ A Bo -- v = E
    +l-E : ∀{A} → E Γ Δ A In → Exp Γ Δ In → E Γ Δ A In                 -- E + e  
    +r-E : ∀{A} → Val In → E Γ Δ A In → E Γ Δ A In -- v + E
    
    call-E : ∀{A n' τ}{Γ' : Ctx n'} → (f : Fun Δ Γ' τ) → FunE Γ Δ Γ' → E Γ Δ A τ
    spawn-E : ∀{A n' τ}{Γ' : Ctx n'} → (f : Fun Δ Γ' τ) → FunE Γ Δ Γ' → E Γ Δ A AR
    spawng-E : ∀{A n' τ}{Γ' : Ctx n'} → (f : Fun Δ Γ' τ) → FunE Γ Δ Γ' → E Γ Δ A AR

    ≔-E : ∀{A τ} → (v : Var Γ τ) → E Γ Δ A τ → E Γ Δ A Un      -- x ≔ E
    ,-E : ∀{A B} → E Γ Δ A Un → Exp Γ Δ B → E Γ Δ A B                 -- E , e
    if-E : ∀{A B} → E Γ Δ A Bo → Exp Γ Δ B → Exp Γ Δ B → E Γ Δ A B     -- If E then e else e
    ignore-E : ∀{A B} → E Γ Δ A B → E Γ Δ A Un -- ignore E
    sendl-E : ∀{A B} → E Γ Δ A AR → Exp Γ Δ B → E Γ Δ A B                 -- send E e
    sendr-E : ∀{A B} → Val AR → E Γ Δ A B → E Γ Δ A B -- send v E

infix 4 _≡_[_]
infix 4 _≡′_[_]

mutual
  data _≡′_[_] {n}{Γ : Ctx n}{m}{Δ : FCtx m} : ∀{φ n'}{ctx : Ctx n'} → ExpList Γ Δ ctx → FunE Γ Δ ctx → Exp Γ Δ φ → Set where
    exp-≡′ : ∀{n'}{ctx : Ctx n'}{φ}{e' : Exp Γ Δ φ}{τ}{E : E Γ Δ φ τ}{e}{l : ExpList Γ Δ ctx} → 
         e ≡ E [ e' ] → 
         e ∷ l ≡′ exp E l [ e' ]
    val-≡′ : ∀{n'}{ctx : Ctx n'}{l}{E : FunE Γ Δ ctx}{τ}{υ : Val τ}{φ}{e : Exp Γ Δ φ} → 
         l ≡′ E [ e ] → 
         (val υ) ∷ l ≡′ val υ E [ e ]

  data _≡_[_] {n m} {Γ : Ctx n} {Δ : FCtx m} : ∀{τ φ} → Exp Γ Δ τ → E Γ Δ φ τ → Exp Γ Δ φ → Set where
    exp-≡ : ∀{τ} {e : Exp Γ Δ τ} → -- e redex →
      e ≡ □ [ e ]
    =l-≡ : ∀{τ φ E} {e₀ e₁ : Exp Γ Δ τ} {e : Exp Γ Δ φ} → e₀ ≡ E [ e ] → 
      e₀ ≐ e₁ ≡ =l-E E e₁ [ e ]
    =r-≡ : ∀{A B E} {e₀ : Val A} {e₁ : Exp Γ Δ A} {e : Exp Γ Δ B} → e₁ ≡ E [ e ] → 
      val e₀ ≐ e₁ ≡ =r-E e₀ E [ e ]
    ¬-≡ : ∀{B E} {e₀ : Exp Γ Δ Bo}{e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
      ¬ e₀ ≡ ¬-E E [ e ]
    +l-≡ : ∀{B E} {e₀ e₁ : Exp Γ Δ In} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
      e₀ ∔ e₁ ≡ +l-E E e₁ [ e ]
    +r-≡ : ∀{B E} {e₀ : Val In} {e₁ : Exp Γ Δ In} {e : Exp Γ Δ B} → e₁ ≡ E [ e ] → 
      val e₀ ∔ e₁ ≡ +r-E e₀ E [ e ]
    ∨l-≡ : ∀{B E} {e₀ e₁ : Exp Γ Δ Bo} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
      e₀ ⊻ e₁ ≡ ∨l-E E e₁ [ e ]
    ∨r-≡ : ∀{B E} {e₀ : Val Bo} {e₁ : Exp Γ Δ Bo} {e : Exp Γ Δ B} → e₁ ≡ E [ e ] → 
      val e₀ ⊻ e₁ ≡ ∨r-E e₀ E [ e ]
    ≔-≡ : ∀{τ φ} {x : Var Γ φ} {e₀ : Exp Γ Δ φ}{e : Exp Γ Δ τ} {E : E Γ Δ τ φ} → e₀ ≡ E [ e ] → 
      x ≔ e₀ ≡ ≔-E x E [ e ]
    if-≡ : ∀{A B E e₀} {e₁ e₂ : Exp Γ Δ A} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
      If e₀ then e₁ else e₂ ≡ if-E E e₁ e₂ [ e ]
    ignore-≡ : ∀{A B E} {e₀ : Exp Γ Δ A}{e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
      ignore e₀ ≡ ignore-E E [ e ]
    sendl-≡ : ∀{A B E e₁} {e₂ : Exp Γ Δ B}{e : Exp Γ Δ A} → e₁ ≡ E [ e ] →
      send e₁ e₂ ≡ sendl-E E e₂ [ e ]
    sendr-≡ : ∀{A B E v₁} {e₂ : Exp Γ Δ B} {e : Exp Γ Δ A} → e₂ ≡ E [ e ] → 
      send (val v₁) e₂ ≡ sendr-E v₁ E [ e ]
    call-≡ : ∀{τ φ n'}{e : Exp Γ Δ τ}{Γ' : Ctx n'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      fun （ args ） ≡ call-E fun E [ e ]
    spawn-≡ : ∀{τ φ n'}{e : Exp Γ Δ τ}{Γ' : Ctx n'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawn fun args ≡ spawn-E fun E [ e ]
    spawng-≡ : ∀{τ φ n'}{e : Exp Γ Δ τ}{Γ' : Ctx n'}{fun : Fun Δ Γ' φ} → ∀{args E} → args ≡′ E [ e ] → 
      spawng fun args ≡ spawng-E fun E [ e ]
    ,-≡ : ∀{τ φ e₀}{e₁ : Exp Γ Δ τ}{E : E Γ Δ φ Un}{e : Exp Γ Δ φ} →  e₀ ≡ E [ e ] → 
      (e₀ , e₁) ≡ ,-E E e₁ [ e ]

  
data EnvF' {m} (Δ : FCtx m) : {m' : ℕ} → FCtx m' → Set where
 [] : EnvF' Δ []
 _∷_ : ∀{ret n m'}{Γ : Vec Type n}{AS : FCtx m'} → Exp Γ Δ ret → EnvF' Δ AS → EnvF' Δ (((n , Γ) , ret) ∷ AS)

EnvF : ∀{m} → FCtx m → Set
EnvF Δ = EnvF' Δ Δ

data Call  {m} (Δ : FCtx m) : Set where
  <_/_> : ∀{φ τ n}{Γ : Ctx n} → E Γ Δ φ τ → State Γ → Call Δ

data Task {m} (Δ : FCtx m) : Set where
  ⟨_,_,_,_⟩ : Queue → ∀{n τ}{Γ : Ctx n} → Exp Γ Δ τ → State Γ → List (Call Δ) → Task Δ

data TaskE {m}{Δ : FCtx m} : Task Δ → Set where
  task-E : ∀{n}{Γ : Ctx n}{τ φ q ρ ts e₀ e} → (E : E Γ Δ τ φ) → e₀ ≡ E [ e ] → TaskE ⟨ q , e₀ , ρ , ts ⟩

data _≡T_[_] {n}{Γ : Ctx n}{m}{Δ : FCtx m} : ∀{φ} → (t : Task Δ) → TaskE t → Exp Γ Δ φ → Set where
  task-≡ : ∀{q ρ ts τ φ}{e₀ : Exp Γ Δ τ}{E : E Γ Δ φ τ}{e : Exp Γ Δ φ} → 
        (p : e₀ ≡ E [ e ]) → 
        ⟨ q , e₀ , ρ , ts ⟩ ≡T task-E E p [ e ]

data Group {m}{Δ : FCtx m}(envF : EnvF Δ) : ℕ → Set where
  group : ∀{n} → Maybe (Fin n) → Vec (Task Δ) n → Group envF n

-- indexed by the number of groups
Cfg : ∀{m}{Δ : FCtx m} → (envF : EnvF Δ) → ℕ → Set
Cfg envF n = Vec (∃ λ m → Group envF m) n


lkp-fun : ∀{m m' n' τ} {Δ : FCtx m} {Δ' : FCtx m'} {Γ' : Ctx n'} → EnvF' Δ' Δ → (f : Fun Δ Γ' τ) → Exp Γ' Δ' τ
lkp-fun []         ()
lkp-fun (y ∷ _)    (z _ _) = y
lkp-fun (_ ∷ envF) (s fun) = lkp-fun envF fun

args-to-state : ∀{τ n m n'}{Γ : Ctx n}{Δ : FCtx m}{Γ' : Ctx n'} → (fun : Fun Δ Γ' τ) → (args : ExpList Γ Δ Γ') → fun （ args ） redex → State Γ'
args-to-state fun args (call-redex p) = a2s' args p
  where a2s' : ∀{n m n'}{Γ : Ctx n}{Δ : FCtx m}{Γ' : Ctx n'} → (args : ExpList Γ Δ Γ') → args values → State Γ'
        a2s' []          []-values = []
        a2s' (._ ∷ args) (∷-values va ._ p) = va ∷ a2s' args p

data Eff : Set where
  none : Eff
  spawn : Eff
  spawng : Eff
  send : ∀{τ} → ARef → Val τ → Eff
  yield : Eff

data _⟶_,_ {m} {Δ : FCtx m} : Task Δ → Task Δ → Eff → Set where
 hole : ∀{q ts A B n} {Γ : Ctx n} {ρ : State Γ} {e e' : Exp Γ Δ B} {E : E Γ Δ A B} {e₀ e₀' : Exp Γ Δ A} → 
     e ≡ E [ e₀ ] → q , e₀ , ρ ↦ e₀' → e' ≡ E [ e₀' ] →
     ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , none
 assign : ∀{q ts B n τ} {Γ : Ctx n} {x : Var Γ τ} {e e' : Exp Γ Δ B} {E : E Γ Δ Un B} {v : Val τ} {ρ : State Γ} → 
     e ≡ E [ x ≔ val v ] → e' ≡ E [ skip ] →
     ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , upd x v ρ , ts ⟩ , none
 synccall : ∀ {q ts A n n' τ} {Γ : Ctx n}{Γ' : Ctx n'} {f : Fun Δ Γ' τ} {args : ExpList Γ Δ Γ'} {E : E Γ Δ τ A} {e : Exp Γ Δ A} {ρ : State Γ} →
     (envF : EnvF Δ) → (z : e ≡ E [ f （ args ） ]) → (r : (f （ args ）) redex) → 
     ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , lkp-fun envF f , args-to-state f args r , < E / ρ > ∷ ts ⟩ , none
 yield⟶ : ∀{n}{Γ : Ctx n}{q ρ ts A}{e e' : Exp Γ Δ A}{E : E Γ Δ Un A} → 
     e ≡ E [ yield ] → e' ≡ E [ skip ] →
     ⟨ q , e , ρ , ts ⟩ ⟶ ⟨ q , e' , ρ , ts ⟩ , yield

--infixr 4 _⇒_ 

--data _⇒_ {m c c'} {Δ : FCtx m} {envF : EnvF Δ} : Cfg envF c → Cfg envF c' → Set where
-- mid : {task : Task Δ}{tasks tasks' : Cfg envF} → 
--     _⇒_ {_} {_} {envF} tasks tasks' →
--     (task ∷ tasks) ⇒ (task ∷ tasks')
-- step-task : ∀{task task' : Task Δ}{tasks : Cfg envF} → 
--     task ⟶ task' →
--     task ∷ tasks ⇒ task' ∷ tasks
-- async-call : 
     