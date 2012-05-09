module Source.Semantics where

open import Data.Nat
open import Data.Vec hiding (group; _∷ʳ_)
open import Data.Bool
open import Data.Maybe
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.List

open import Source.Syntax
open import Source.EvalCtx
open import Source.Substitution
open import Utils

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


a2s : ∀{Γ Δ Ξ Λ} → (args : ExpList Γ Δ Ξ Λ) → args values → State Λ
a2s []          []-values = []
a2s (._ ∷ args) (∷-values va ._ p) = va ∷ a2s args p

args-to-state : ∀{τ Γ Ξ Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ Λ) → fun （ args ） redex → State Λ
args-to-state fun args (call-redex x) = a2s args x

spawn-args-to-state : ∀{τ Γ Ξ Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ Λ) → spawn fun args redex → State Λ
spawn-args-to-state fun args (spawn-redex x) = a2s args x

spawng-args-to-state : ∀{τ Γ Ξ Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ Λ) → spawng fun args redex → State Λ
spawng-args-to-state fun args (spawng-redex x) = a2s args x

data EnvF' (Δ : FCtx) : FCtx → Set where
 [] : EnvF' Δ []
 _∷_ : ∀{Γ φ Φ} → Exp Δ Γ [] φ → EnvF' Δ Φ → EnvF' Δ ((Γ , φ) ∷ Φ)

EnvF : FCtx → Set
EnvF Δ = EnvF' Δ Δ

lkp-fun : ∀{Δ Γ' Δ' τ} → EnvF' Δ' Δ → (f : Fun Δ Γ' τ) → Exp Δ' Γ' [] τ
lkp-fun []         ()
lkp-fun (f ∷ _)    (z ._ ._) = f
lkp-fun (_ ∷ envF) (s fun)   = lkp-fun envF fun


send-local : ∀{Δ n τ} → TaskID n → Val τ → Vec (Task Δ) n → Vec (Task Δ) n
send-local zero      v (⟨ q , e , ρ , cs ⟩ ∷ ts) = ⟨ q ∷ʳ (_ , v ) , e , ρ , cs ⟩ ∷ ts
send-local (suc tid) v (t ∷ ts) = t ∷ send-local tid v ts

send-global : ∀{τ n}{ts : Vec ℕ n} → (gid : GroupID n) → TaskID (lookup gid ts) → Val τ → Cfg ts → Cfg ts
send-global zero      tid v ((group x ts) ∷ gs) = group x (send-local tid v ts) ∷ gs
send-global (suc gid) tid v (g ∷ gs)            = g ∷ send-global gid tid v gs

--
-- Layer 1 : task
--

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
  -- things handled in outer layers : spawn , spawng , yield , send

--
-- Layer 2 : group
--


data _∈_executable {Δ} : ∀{n} → (x : Fin n) → Vec (Task Δ) n → Set where
  -- if it is a value, then we can return to something and take a step 
  z-call-ex : ∀{Γ q ρ τ cs n}{ts : Vec (Task Δ) n}{e : Exp Δ Γ [] τ}{c : Call Δ} → 
    zero ∈ ⟨ q , e , ρ , c ∷ cs ⟩ ∷ ts executable
  z-root-ex : ∀{Γ q ρ τ n}{ts : Vec (Task Δ) n}{e : Exp Δ Γ [] τ}{φ}{e' : Exp Δ Γ [] φ}{E} → 
    e ≡ E [ e' ] → e' redex → 
    zero ∈ ⟨ q , e , ρ , [] ⟩ ∷ ts executable
  s-ex : ∀{n}{x : Fin n}{ts : Vec (Task Δ) n}{t} → 
    x ∈ ts executable → 
    (suc x) ∈ t ∷ ts executable

--_of_executable : ∀{Δ n} → (x : Fin n) → Vec (Task Δ) n → Set
--zero of ⟨ x , x₁ , x₂ , x₃ ⟩ ∷ ts executable = {!!}
--suc x of _ ∷ ts executable = x of ts executable

data _⟶g_ {Δ} : ∀{n n'} → Group Δ n → Group Δ n' → Set where
  step⟶g : ∀{task task' n g g'}{m : Fin n}{E : GroupE Δ n m} → 
     task ⟶t task' → 
     g ≡G E [ task ] → g' ≡G E [ task' ] → 
     g ⟶g g'
  yield⟶g : ∀{Γ n}{x : Fin n}{tasks tasks' : Vec (Task Δ) n}{τ}{e e' : Exp Δ Γ [] τ}{E₂ : E Δ Γ [] Un τ}{q ρ cs}{E : GroupE Δ n x} → 
    e ≡ E₂ [ yield ] → e' ≡ E₂ [ skip ] → 
    group (just x) tasks ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → group nothing tasks' ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] →   
    group (just x) tasks ⟶g group nothing tasks'
  schedule⟶g : ∀{n}{tasks : Vec (Task Δ) n}{x : Fin n} →
    x ∈ tasks executable → 
    group nothing tasks ⟶g group (just x) tasks

--
-- Layer 3 : configurations
--

infixr 5 _⟶c_

data _⟶c_ {Δ} : ∀{n m}{S : Vec ℕ n}{T : Vec ℕ m} → Cfg S → Cfg T → Set where
  step⟶c : ∀{n gid}{S T : Vec ℕ n}{cfg cfg' : Cfg S}{g g' : Group Δ (lookup gid S)}{E : CfgE gid S} → 
    g ⟶g g' → 
    cfg ≡C E [ g ] → cfg' ≡C E [ g' ] →
    cfg ⟶c cfg'
  send⟶c : ∀{n gid}{S : Vec ℕ n}{cfg cfg' : Cfg S}{E₁ : CfgE gid S}{g g' Γ φ τ}{e e' : Exp Δ Γ [] τ}{q ρ cs x}{E₂ : GroupE Δ (lookup gid S) x}{E₃ : E Δ Γ [] φ τ}{msg : Val φ}{grp : Fin n}{tsk : Fin (lookup grp S)} → 
    e ≡ E₃ [ send (val (A n (lookup grp S) (AR grp tsk))) (val msg) ] → e' ≡ E₃ [ val msg ] → -- (AR grp task))) (val msg) ] → e' ≡ E₃ [ val msg ] → 
    g ≡G E₂ [ ⟨ q , e , ρ , cs ⟩ ] → g' ≡G E₂ [ ⟨ q , e' , ρ , cs ⟩ ] → 
    cfg ≡C E₁ [ g ] → cfg' ≡C E₁ [ g' ] → 
    cfg ⟶c cfg'
{-
  spawng⟶c : ∀{n m gid}{cfg cfg' : Cfg Δ n}{E₁ : CfgE Δ n gid}{g g' : Group Δ m}{Γ τ}{e e' : Exp Δ Γ [] τ}{q ρ cs}{x : Fin m}{E₂ : GroupE Δ m x}{E₃ : E Δ Γ [] AR τ}{Λ φ}{fun : Fun Δ Λ φ}{args} → 
    (envF : EnvF Δ) → (p : spawng fun args redex) → 
    e ≡ E₃ [ spawng fun args ] → e' ≡ E₃ [ val (A {!!} {!!} (AR {!!} {!!})) ] → -- (AR n 0)) ] → 
    g ≡G E₂ [ ⟨ q , e , ρ , cs ⟩ ] → g' ≡G E₂ [ ⟨ q , e' , ρ , cs ⟩ ] → 
    cfg ≡C E₁ [ m , g ] → cfg' ≡C E₁ [ m , g' ] → 
    cfg ⟶c (suc zero , group (just zero) Data.Vec.[ ⟨ [] , lkp-fun envF fun , spawng-args-to-state fun args p , [] ⟩ ]) ∷ cfg'
  send⟶c : ∀{n m gid}{cfg cfg' : Cfg Δ n}{E₁ : CfgE Δ n gid}{g g' : Group Δ m}{Γ φ τ}{e e' : Exp Δ Γ [] τ}{q ρ cs}{x : Fin m}{E₂ : GroupE Δ m x}{E₃ : E Δ Γ [] φ τ}{msg : Val φ}{grp task} → 
    e ≡ E₃ [ send (val (A {!!} {!!} (AR {!!} {!!}))) (val msg) ] → e' ≡ E₃ [ val msg ] → -- (AR grp task))) (val msg) ] → e' ≡ E₃ [ val msg ] → 
    g ≡G E₂ [ ⟨ q , e , ρ , cs ⟩ ] → g' ≡G E₂ [ ⟨ q , e' , ρ , cs ⟩ ] → 
    cfg ≡C E₁ [ m , g ] → cfg' ≡C E₁ [ m , g' ] → 
    cfg ⟶c cfg'
-}
{-
-- maybe move to outher level
  spawn⟶g : ∀{Γ n}{x : Fin n}{tasks tasks' : Vec (Task Δ) n}{τ}{e e' : Exp Δ Γ [] τ}{E₂ : E Δ Γ [] AR τ}{q ρ cs}{E : GroupE Δ n x}{Λ φ}{f : Fun Δ Λ φ}{args gid} → 
    (envF : EnvF Δ) → (p : spawn f args redex) → 
    e ≡ E₂ [ spawn f args ] → e' ≡ E₂ [ val (A {!!} {!!} (AR {!!} {!!} )) ] → -- gid n)) ] →
    group (just x) tasks ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → group (just x) tasks' ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] → 
    [ gid ] group (just x) tasks ⟶g group (just (inject₁ x)) (tasks Data.Vec.∷ʳ ⟨ [] , lkp-fun envF f  , spawn-args-to-state f args p  , [] ⟩)
  send-local⟶g : ∀{gid Γ n}{x : Fin n}{tasks tasks' : Vec (Task Δ) n}{τ φ}{e e' : Exp Δ Γ [] τ}{E₂ : E Δ Γ [] φ τ}{q ρ cs}{E : GroupE Δ n x}{recv msg} → 
    e ≡ E₂ [ send (val (A {!!} {!!} (AR {!!} {!!}))) (val msg) ] → e' ≡ E₂ [ val msg ] → -- (AR gid recv))) (val msg) ] → e' ≡ E₂ [ val msg ] → 
    group (just x) tasks ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → group (just x) tasks' ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] →   
    [ gid ] group (just x) tasks ⟶g group (just x) (send-local recv msg tasks)
-}