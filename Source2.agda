-- {-# OPTIONS --type-in-type #-}
module Source2 where

open import Data.Bool
open import Data.Unit 
open import Data.List
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Product

_≡b_ : Bool → Bool → Bool
true ≡b true = true
false ≡b false = true
_ ≡b _ = false

_≡n_ : ℕ → ℕ → Bool
zero ≡n zero = true
zero ≡n (suc _) = false
(suc _) ≡n zero = false
(suc a) ≡n (suc b) = a ≡n b

-- base types
data Type : Set where
  Un : Type
  Bo : Type
  In : Type
  AR : Type

-- variable context: maps variables to their types
Ctx : ℕ → Set
Ctx n = Vec Type n

-- function contxt: maps functions to parameter types and return type
FCtx : ℕ → Set
--FCtx m = Vec (List Type × Type) m
FCtx m = Vec ((∃ λ (n : ℕ) → Vec Type n) × Type) m
--FCtx m = Vec ((∀{n} → Vec Type n) × Type) m

mutual
  -- list of expressions
  data ExpList {n m} (Γ : Ctx n)(Δ : FCtx m) : {n : ℕ} → Vec Type n → Set where
    s : ExpList Γ Δ []
    c : ∀{φ l}{Φ : Vec Type l} → Exp Γ Δ φ → ExpList Γ Δ Φ → ExpList Γ Δ (φ ∷ Φ) -- (l , AS) → ExpList Γ Δ (suc l , A ∷ AS)

  -- pattern matching on receive
  data Match {n m} (Γ : Ctx n) (Δ : FCtx m) : Type → Set where
    case_⇒_ : ∀{φ} → Fin n → Exp Γ Δ φ → Match Γ Δ φ

  data Exp {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Set where
    U : Exp Γ Δ Un
    A : ℕ → Exp Γ Δ AR
    var : (v : Fin n) → Exp Γ Δ (lookup v Γ)
    N : ℕ → Exp Γ Δ In
    B : Bool → Exp Γ Δ Bo
    _≐_ : {A : Type} → Exp Γ Δ A → Exp Γ Δ A → Exp Γ Δ Bo
    ¬_ : Exp Γ Δ Bo → Exp Γ Δ Bo
    _∔_ : Exp Γ Δ In → Exp Γ Δ In → Exp Γ Δ In
    _⊻_ : Exp Γ Δ Bo → Exp Γ Δ Bo → Exp Γ Δ Bo
    avail : Exp Γ Δ Bo
    _（_） : (f : Fin m) → ExpList Γ Δ (proj₂ (proj₁ (lookup f Δ))) → Exp Γ Δ (proj₂ (lookup f Δ)) -- (proj₁ (lookup f Δ)) → Exp Γ Δ (proj₂ (lookup f Δ))
    spawn : (f : Fin m) → ExpList Γ Δ (proj₂ (proj₁ (lookup f Δ))) → Exp Γ Δ AR -- (proj₁ (lookup f Δ)) → Exp Γ Δ AR
-- placeholder for return value
    ph : (A : Type) → Exp Γ Δ A
-- former statements
    _≔_ : (v : Fin n) → Exp Γ Δ (lookup v Γ) → Exp Γ Δ Un -- Exp Γ Δ (lookup v Γ)
    skip : Exp Γ Δ Un
    _,_ : ∀{A} → Exp Γ Δ Un → Exp Γ Δ A → Exp Γ Δ A -- TODO make sure that first exp doesn't return
    If_then_else_ : ∀{A} → Exp Γ Δ Bo → Exp Γ Δ A → Exp Γ Δ A → Exp Γ Δ A
    While_do_ : Exp Γ Δ Bo → Exp Γ Δ Un → Exp Γ Δ Un -- TODO generalize it to A, not just unit
    send : ∀{A} → Exp Γ Δ AR → Exp Γ Δ A → Exp Γ Δ A
    receive : ∀{A} → List (Match Γ Δ A) → Exp Γ Δ A
    ignore : ∀{A} → Exp Γ Δ A → Exp Γ Δ Un
--    return : ∀{A} → Exp Γ Δ A → Exp Γ Δ A  -- no need for explicit return anymore?

data _value {n m} {Γ : Ctx n}{Δ : FCtx m} : ∀{A} → Exp Γ Δ A → Set where
  uval : U value                 -- unit
--  tval : true value            -- bool
--  fval : false value           -- bool
  bval : {v : Bool} → B v value  -- bool
  nval : {v : ℕ} → N v value   -- int
  aval : {v : ℕ} → A v value     -- actor ref

transval : ∀{n n' m φ} {Γ : Ctx n} {Δ : FCtx m} {Γ' : Ctx n'} → (e : Exp Γ Δ φ) → e value → ∃ λ (e' : Exp Γ' Δ φ) → e' value
transval ._ uval       = U , uval
transval ._ (bval {v}) = B v , bval
transval ._ (nval {v}) = N v , nval
transval ._ (aval {v}) = A v , aval
{-
mutual
  data Match {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Set where
    case_∷_⇒_ : ∀{A} → Fin n → Type → Stmt Γ Δ A → Match Γ Δ A

  data Stmt {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Set where
    _≔_ : (v : Fin n) → Exp Γ Δ (lookup v Γ) → Stmt Γ Δ Un
    skip : Stmt Γ Δ Un
    _,_ : ∀{A} → Stmt Γ Δ Un → Stmt Γ Δ A → Stmt Γ Δ A -- can't sequence something that returns with something else
    If_then_else_ : ∀{A} → Exp Γ Δ Bo → Stmt Γ Δ A → Stmt Γ Δ A → Stmt Γ Δ A
    while_do_ : ∀{A} → Exp Γ Δ Bo → Stmt Γ Δ A → Stmt Γ Δ A
    send : ∀{A} → Exp Γ Δ AR → Exp Γ Δ A → Stmt Γ Δ Un
    return : ∀{A} → Exp Γ Δ A → Stmt Γ Δ A
    receive : ∀{A} → List (Match Γ Δ A) → Stmt Γ Δ A
--    e : ∀{A} → Exp Γ Δ A → Stmt Γ Δ Un
-}

data State' {n m} (Γ : Ctx n) (Δ : FCtx m) : {n' : ℕ} → Ctx n' → Set where
 [] : State' Γ Δ []
 _∷_ : ∀{A n'}{AS : Ctx n'} → (∃ λ (e : Exp Γ Δ A) → e value) → State' Γ Δ AS → State' Γ Δ (A ∷ AS)

State : ∀{n m} → Ctx n → FCtx m → Set
State Γ Δ = State' Γ Δ Γ

lkp : ∀{n m} {Γ : Ctx n} {Δ : FCtx m} → State Γ Δ → (x : Fin n) → ∃ λ (e : Exp Γ Δ (lookup x Γ)) → e value
lkp ss x = lkp' ss x -- Γ' is Γ
  where lkp' : ∀{n m n'}{Γ : Ctx n}{Δ : FCtx m}{Γ' : Ctx n'} → State' Γ Δ Γ' → (x : Fin n') → ∃ λ (e : Exp Γ Δ (lookup x Γ')) → e value
        lkp' []       ()
        lkp' (v ∷ _)  zero    = v
        lkp' (_ ∷ st) (suc x) = lkp' st x

upd : ∀{n m} {Γ : Ctx n} {Δ : FCtx m} → (x : Fin n) → (e : Exp Γ Δ (lookup x Γ)) → e value → State Γ Δ → State Γ Δ
upd x e p = upd' x e p
  where upd' : ∀{n m n'}{Γ : Ctx n}{Δ : FCtx m}{Γ' : Ctx n'} → (x : Fin n') → (e : Exp Γ Δ (lookup x Γ')) → e value → State' Γ Δ Γ' → State' Γ Δ Γ'
        upd' zero    e p (_ ∷ st) = (e , p) ∷ st
        upd' (suc x) e p (v ∷ st) = v ∷ upd' x e p st

-- append messages to the end, pop them from the head
Queue : ∀{m} → FCtx m → Set
Queue Δ = List (∃₂ λ n (Γ : Ctx n) → ∃₂ λ A (e : Exp Γ Δ A) → e value)

data _,_,_↦_ {n m} {Γ : Ctx n} {Δ : FCtx m} : ∀{A} → Queue Δ → Exp Γ Δ A → State Γ Δ → Exp Γ Δ A → Set where
  Var↦ : ∀{q v ρ} →
    q , var v , ρ ↦ proj₁ (lkp ρ v) -- ⟨ q , proj₁ (proj₂ (ρ v)) , ρ ⟩
  ∔↦ : ∀{q v₁ v₂ ρ} → 
    q , N v₁ ∔ N v₂ , ρ ↦ N (v₁ + v₂) -- ⟨ q , N (v₁ + v₂) , ρ ⟩
  ⊻↦ : ∀{q v₁ v₂ ρ} → 
    q , B v₁ ⊻ B v₂ , ρ ↦ B (v₁ ∨ v₂) -- ⟨ q , B (v₁ ∨ v₂) , ρ ⟩
  ¬↦ : ∀{q v ρ} → 
    q , ¬ B v , ρ ↦ B (not v) -- ⟨ q , B (not v) , ρ ⟩
  avail-true : ∀{m q ρ} → 
    (m ∷ q) , avail , ρ ↦ B true -- ⟨ m ∷ q , B true , ρ ⟩
  avail-false : ∀{ρ} → 
    [] , avail , ρ ↦ B false -- ⟨ [] , B false , ρ ⟩
  ≐↦-int : ∀{q v₁ v₂ ρ} → 
    q , N v₁ ≐ N v₂ , ρ ↦ B (v₁ ≡n v₂) -- ⟨ q , B (v₁ ≡n v₂) , ρ ⟩ 
  ≐↦-bool : ∀{q v₁ v₂ ρ} → 
    q , B v₁ ≐ B v₂ , ρ ↦ B (v₁ ≡b v₂) -- ⟨ q , B (v₁ ≡b v₂) , ρ ⟩ 
-- some of stmts
  skip↦ : ∀{q ρ A} {e : Exp Γ Δ A} → 
    q , (skip , e) , ρ ↦ e
  IfT↦ : ∀ {q ρ A} {e₁ e₂ : Exp Γ Δ A} →
    q , If (B true) then e₁ else e₂ , ρ ↦ e₁
  IfF↦ : ∀{q ρ A} {e₁ e₂ : Exp Γ Δ A} → 
    q , If (B false) then e₁ else e₂ , ρ ↦ e₂
  While : ∀{q e' e ρ} → 
    q , While e do e' , ρ ↦ If e then (e' , While e do e') else skip
--  WhileT : ∀{q e' e ρ} → -- {e : Exp Γ Δ A} → 
--    q , While (B true) / e' do e , ρ ↦ (e , While e' / e' do e)
--  WhileF : ∀{q e' e ρ} → -- {e : Exp Γ Δ A} → 
--    q , While (B false) / e' do e , ρ ↦ skip

{-
data Task {n m} (Γ : Ctx n)(Δ : FCtx m) : Set where
  <_/_> : ∀{A} → Stmt Γ Δ A → State Γ Δ → Task Γ Δ

Stack : ∀{n m} → Ctx n → FCtx m → Set
Stack Γ Δ = List (Task Γ Δ)

data StmtCfg {n m} (Γ : Ctx n)(Δ : FCtx m) : Set where
 ⟨_,_⟩ : Queue Γ Δ → Stack Γ Δ → StmtCfg Γ Δ
-}
-- evaluation ctx, indexed by the type of the hole and the return type
mutual
  -- convention: τ is the type expected in the hole, φ is the return type

  data FunE {n m} (Γ : Ctx n) (Δ : FCtx m) : {n' : ℕ} → Vec Type n' → Type → Set where
    e : ∀{τ} → FunE Γ Δ [] τ
    h : ∀{τ φ n'}{Φ : Vec Type n'} → E Γ Δ τ φ → ExpList Γ Δ Φ → FunE Γ Δ (φ ∷ Φ) τ
    v : ∀{τ φ n'}{Φ : Vec Type n'} → (e : Exp Γ Δ φ) → e value → FunE Γ Δ Φ τ → FunE Γ Δ (φ ∷ Φ) τ

  -- Eval ctx : variable context, function context, type expected in the hole, return type
  data E {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Type → Set where
    □  : ∀{τ} → E Γ Δ τ τ
    ¬s : ∀{τ} → E Γ Δ τ Bo → E Γ Δ τ Bo                              -- ¬ E
    ∨l : ∀{A} → E Γ Δ A Bo → Exp Γ Δ Bo → E Γ Δ A Bo                 -- E ∨ e  
    ∨r : ∀{A} → (e : Exp Γ Δ Bo) → e value → E Γ Δ A Bo → E Γ Δ A Bo -- v ∨ E -- what about true ∨ E ?
    =l : ∀{τ φ} → E Γ Δ τ φ → Exp Γ Δ φ → E Γ Δ τ Bo                 -- E = e
    =r : ∀{A B} → (e : Exp Γ Δ B) → e value → E Γ Δ A B → E Γ Δ A Bo -- v = E
    +l : ∀{A} → E Γ Δ A In → Exp Γ Δ In → E Γ Δ A In                 -- E + e  
    +r : ∀{A} → (e : Exp Γ Δ In) → e value → E Γ Δ A In → E Γ Δ A In -- v + E
    
--    fs : ∀{A} → (f : Fin m) → FunE Γ Δ (proj₂ (proj₁ (lookup f Δ))) A → E Γ Δ A (proj₂ (lookup f Δ))
--    fa : ∀{A} → (f : Fin m) → FunE Γ Δ (proj₂ (proj₁ (lookup f Δ))) A → E Γ Δ A AR

    ≔s : ∀{A} → (v : Fin n) → E Γ Δ A (lookup v Γ) → E Γ Δ A Un      -- x ≔ E
    se : ∀{A B} → E Γ Δ A Un → Exp Γ Δ B → E Γ Δ A B                 -- E , e
    if : ∀{A B} → E Γ Δ A Bo → Exp Γ Δ B → Exp Γ Δ B → E Γ Δ A B     -- If E then e else e
--    wh : ∀{A} → E Γ Δ A Bo → Exp Γ Δ Un → E Γ Δ A Un                 -- While E do e

data _≡_[_] {n m} {Γ : Ctx n} {Δ : FCtx m} : ∀{A B} → Exp Γ Δ A → E Γ Δ B A → Exp Γ Δ B → Set where
  a : ∀{A} {e : Exp Γ Δ A} →
    e ≡ □ [ e ]
  b : ∀{A B E} {e₀ e₁ : Exp Γ Δ A} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
    (e₀ ≐ e₁) ≡ =l E e₁ [ e ]
  c : ∀{A B E} {e₀ e₁ : Exp Γ Δ A} {e : Exp Γ Δ B} → (p : e₀ value) → e₁ ≡ E [ e ] → 
    (e₀ ≐ e₁) ≡ =r e₀ p E [ e ]
  d : ∀{B E} {e₀ : Exp Γ Δ Bo}{e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
    (¬ e₀) ≡ ¬s E [ e ]
  e : ∀{B E} {e₀ e₁ : Exp Γ Δ In} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
    (e₀ ∔ e₁) ≡ +l E e₁ [ e ]
  f : ∀{B E} {e₀ e₁ : Exp Γ Δ In} {e : Exp Γ Δ B} → (p : e₀ value) → e₁ ≡ E [ e ] → 
    (e₀ ∔ e₁) ≡ +r e₀ p E [ e ]
  g : ∀{B E} {e₀ e₁ : Exp Γ Δ Bo} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
    (e₀ ⊻ e₁) ≡ ∨l E e₁ [ e ]
  h : ∀{B E} {e₀ e₁ : Exp Γ Δ Bo} {e : Exp Γ Δ B} → (p : e₀ value) → e₁ ≡ E [ e ] → 
    (e₀ ⊻ e₁) ≡ ∨r e₀ p E [ e ]
  i : ∀{τ} {x : Fin n} {e₀ : Exp Γ Δ (lookup x Γ)}{e : Exp Γ Δ τ} {E : E Γ Δ τ (lookup x Γ)} → e₀ ≡ E [ e ] → 
    (x ≔ e₀) ≡ ≔s x E  [ e ]
  j : ∀{A B E e₀} {e₁ e₂ : Exp Γ Δ A} {e : Exp Γ Δ B} → e₀ ≡ E [ e ] → 
    (If e₀ then e₁ else e₂) ≡ if E e₁ e₂ [ e ]
--  k : ∀{B E e₀ e₁ e₂}{e : Exp Γ Δ B} →  e₀ ≡ E [ e ] → 
--    (While e₀ / e₁ do e₂) ≡ wh E e₂ [ e ]
  -- function calls

-- nomenclature!
data Task {m} (Δ : FCtx m) : Set where
  <_/_> : ∀{A n}{Γ : Ctx n} → Exp Γ Δ A → State Γ Δ → Task Δ

-- Task
data Cfg {m} (Δ : FCtx m) : Set where
  ⟨_,_⟩ : Queue Δ → List (Task Δ) → Cfg Δ

--data EnvF {n m} (Γ : Ctx n) (Δ : FCtx m) : Set where
--  z : Exp Γ Δ (proj₂ (lookup {!zero!} Δ)) → EnvF Γ Δ

data EnvF' {m} (Δ : FCtx m) : {m' : ℕ} → FCtx m' → Set where
 [] : EnvF' Δ []
 _∷_ : ∀{ret n m'}{Γ : Vec Type n}{AS : FCtx m'} → Exp Γ Δ ret → EnvF' Δ AS → EnvF' Δ (((n , Γ) , ret) ∷ AS)

EnvF : ∀{m} → FCtx m → Set
EnvF Δ = EnvF' Δ Δ

lkp-fun : ∀{m m'} {Δ : FCtx m} {Δ' : FCtx m'} → EnvF' Δ' Δ → (f : Fin m) → Exp (proj₂ (proj₁ (lookup f Δ))) Δ' (proj₂ (lookup f Δ))
lkp-fun []         ()
lkp-fun (exp ∷ _)  zero      = exp
lkp-fun (_ ∷ envF) (suc fun) = lkp-fun envF fun

data _⟶_ {m} {Δ : FCtx m} : Cfg Δ → Cfg Δ → Set where
 hole : ∀{q ts A B n} {Γ : Ctx n} {ρ : State Γ Δ} {e e' : Exp Γ Δ B} {E : E Γ Δ A B} {e₀ e₀' : Exp Γ Δ A} → 
     e ≡ E [ e₀ ] → q , e₀ , ρ ↦ e₀' → e' ≡ E [ e₀' ] →
     ⟨ q , < e / ρ > ∷ ts ⟩ ⟶ ⟨ q , < e' / ρ > ∷ ts ⟩
 assign : ∀{q ts B n} {x : Fin n} {Γ : Ctx n} {e e' : Exp Γ Δ B} {E : E Γ Δ Un B} {v : Exp Γ Δ (lookup x Γ)} {ρ : State Γ Δ} → 
     e ≡ E [ x ≔ v ] → (p : v value) → e' ≡ E [ skip ] →
     ⟨ q , < e / ρ > ∷ ts ⟩ ⟶ ⟨ q , < e' / upd x v p ρ > ∷ ts ⟩
 synccall : ∀ {q ts A n} {Γ : Ctx n} {f : Fin m} {args : ExpList Γ Δ (proj₂ (proj₁ (lookup f Δ)))} {E : E Γ Δ (proj₂ (lookup f Δ)) A} {e e' : Exp Γ Δ A} {ρ : State Γ Δ} →
     (envF : EnvF Δ) → (z : e ≡ E [ f （ args ） ]) → e' ≡ E [ ph (proj₂ (lookup f Δ)) ] →
     ⟨ q , < e / ρ > ∷ ts ⟩ ⟶ ⟨ q , < lkp-fun envF f / {!!} > ∷ < e' / ρ > ∷ ts ⟩

l2s : ∀{n m} {Γ : Ctx n} {Δ : FCtx m} {f : Fin m} → ExpList Γ Δ (proj₂ (proj₁ (lookup f Δ))) → State (proj₂ (proj₁ (lookup f Δ))) Δ
l2s el = {!!}

--data ECfg {n m} (Γ : Ctx n)(Δ : FCtx m) : Set where
-- ⟨_,_,_⟩ : ∀{A} → Queue Γ Δ → Exp Γ Δ A → State Γ Δ → ExpCfg Γ Δ
--data _⟶e_ {n m} {Γ : Ctx n} {Δ : FCtx m} : Set where

{- 
-- reduction of expressions
data ⟨_,_,_⟩⟶e⟨_,_,_⟩ {n m} {Γ : Ctx n} {Δ : FCtx m} : ∀{A} → Queue Γ Δ → Exp Γ Δ A → State Γ Δ →  Queue Γ Δ → Exp Γ Δ A → State Γ Δ → Set where
  a : ∀{e e' e₀ e₀' E q ρ} → e ≡ E [ e₀ ] → q , e₀ , ρ ↦ e₀' → e' ≡ E [ e₀' ] →
    ⟨ q , e , ρ ⟩⟶e⟨ q , e' , ρ ⟩ 
--  q , e , ρ ↦ e'

-- eval ctx for statements
data ES {n m} (Γ : Ctx n)(Δ : FCtx m) : Type → Set where
  □ : ∀{A} → ES Γ Δ A
  seq : ∀{A} → Stmt Γ Δ A → ES Γ Δ A → ES Γ Δ A -- E ; s
  
data _⟶_ {n m} {Γ : Ctx n} {Δ : FCtx m} : StmtCfg Γ Δ → StmtCfg Γ Δ → Set where
-- ⟨ q , ⟨ q , < S / ρ > ∷ s ⟩ ⟶ ⟨ q' , < S' / ρ' > ∷ s ⟩

-}