module Source.Semantics where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Fin hiding (_+_)
open import Data.Product
open import Data.List hiding ([_])

open import Source.Syntax
open import Source.EvalCtx
open import Source.Substitution
open import Source.Extend
open import Source.ExtendT

open import Util.Vector
open import Util.Eq

data _redex {Γ Δ T Ξ} : ∀{τ} → Exp Δ Γ Ξ T τ → Set where
  var-redex     : ∀{τ}{v : Var Γ τ} → (var v) redex
  =-redex       : ∀{τ}{v₁ v₂ : Val T τ} → ((val v₁) ≐ (val v₂)) redex
  +-redex       : ∀{v₁ v₂} → (val v₁ ∔ val v₂) redex
  ∨-redex       : ∀{v₁ v₂} → (val v₁ ⊻ val v₂) redex
  ¬-redex       : ∀{v} → (¬ val v) redex
  avail-redex   : avail redex
  ≔-redex       : ∀{τ v}{x : Var Γ τ} → (x ≔ val v) redex
  skip-redex    : skip redex
  ,-redex       : ∀{τ}{e : Exp Δ Γ Ξ T τ} → (val U , e) redex
  ignore-redex  : ∀{τ}{v : Val T τ} → ignore (val v) redex
  if-redex      : ∀{τ v}{e₁ e₂ : Exp Δ Γ Ξ T τ} → (If (val v) then e₁ else e₂) redex
  while-redex   : ∀{e₀}{e : Exp Δ Γ Ξ T Un} → (While e₀ do e) redex
  send-redex    : ∀{τ v₁}{v₂ : Val T τ} → send (val v₁) (val v₂) redex
  receive-redex : ∀{τ}{e₁ : Exp Δ Γ (Un ∷ Ξ) T τ}{e₂ : Exp Δ Γ (AR ∷ Ξ) T τ}{e₃ : Exp Δ Γ (In ∷ Ξ) T τ}{e₄ : Exp Δ Γ (Bo ∷ Ξ) T τ} → receive e₁ e₂ e₃ e₄ redex
  call-redex    : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (fun （ args ）) redex
  spawn-redex   : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (spawn fun args) redex
  spawng-redex  : ∀{τ Γ'}{fun : Fun Δ Γ' τ}{args} → args values → (spawng fun args) redex
  yield-redex   : yield redex
  Let-redex     : ∀{τ ξ}{v : Val T ξ}{e : Exp Δ Γ (ξ ∷ Ξ) T τ} → Let (val v) e redex


a2s : ∀{Γ Δ Ξ T Λ} → (args : ExpList Γ Δ Ξ T Λ) → args values → State T Λ
a2s []          []-values = []
a2s (._ ∷ args) (∷-values va ._ p) = va ∷ a2s args p

args-to-state : ∀{τ Γ Ξ T Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ T Λ) → fun （ args ） redex → State T Λ
args-to-state fun args (call-redex x) = a2s args x

spawn-args-to-state : ∀{τ Γ Ξ T Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ T Λ) → spawn fun args redex → State T Λ
spawn-args-to-state fun args (spawn-redex x) = a2s args x

spawng-args-to-state : ∀{τ Γ Ξ T Δ Λ} → (fun : Fun Δ Λ τ) → (args : ExpList Δ Γ Ξ T Λ) → spawng fun args redex → State T Λ
spawng-args-to-state fun args (spawng-redex x) = a2s args x

data EnvF' (Δ : FCtx)(T : TCtx) : FCtx → Set where
 [] : EnvF' Δ T []
 _∷_ : ∀{Γ φ Φ} → Exp Δ Γ [] T φ → EnvF' Δ T Φ → EnvF' Δ T ((Γ , φ) ∷ Φ)

EnvF : FCtx → TCtx → Set
EnvF Δ T = EnvF' Δ T Δ

lkp-fun : ∀{Δ Γ' Δ' T τ} → EnvF' Δ' T Δ → (f : Fun Δ Γ' τ) → Exp Δ' Γ' [] T τ
lkp-fun []         ()
lkp-fun (f ∷ _)    (z ._ ._) = f
lkp-fun (_ ∷ envF) (s fun)   = lkp-fun envF fun

deliver-local : ∀{n Δ T τ} → Fin n → Val T τ → Group Δ T n → Group Δ T n
deliver-local tid v (group-busy tasks₁ task tasks₂) with lookup₂ tid tasks₁ task tasks₂
... | ⟨ q , e , ρ , ts ⟩ with tasks₁ & task & tasks₂ [ tid ]≔ ⟨ q Data.List.∷ʳ (_ , v) , e , ρ , ts ⟩
...     | l , x , r = group-busy l x r

deliver-local tid v (group-idle tasks) with lookup tid tasks
... | ⟨ q , e , ρ , ts ⟩ = group-idle (tasks [ tid ]≔ ⟨ q Data.List.∷ʳ (_ , v)  , e , ρ , ts ⟩)

deliver : ∀{Δ T' T n τ idx} → TaskID T' n → Val T τ → Cfg' {Δ} T T' idx → Cfg' {Δ} T T' idx
deliver task v [] = []
deliver {n = n} task v (grp ∷ cfg) with down _ n
... | nothing = deliver-local task v grp ∷ cfg
... | just x  = grp ∷ deliver {n = x} task v cfg

--
-- Layer 1 : task
--

data _,_,_⟶e_,_,_ {T Γ Δ Ξ} : ∀{τ} → Queue T → Exp Δ Γ Ξ T τ → State T Γ → Queue T → Exp Δ Γ Ξ T τ → State T Γ → Set where
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
  seq↦ : ∀{q ρ τ} {e : Exp Δ Γ Ξ T τ} →
         q , (val U , e)                  , ρ ⟶e       q , e                  , ρ
  IfT↦ : ∀ {q ρ τ} {e₁ e₂ : Exp Δ Γ Ξ T τ} → 
         q , If (val (B true)) then e₁ else e₂  , ρ ⟶e q , e₁ , ρ
  IfF↦ : ∀{q ρ τ} {e₁ e₂ : Exp Δ Γ Ξ T τ} → 
         q , If (val (B false)) then e₁ else e₂ , ρ ⟶e q , e₂ , ρ
  While↦ : ∀{q e' e ρ} →
         q , While e do e'                      , ρ ⟶e q , If e then (e' , While e do e') else skip , ρ
  ignore↦ : ∀{q τ ρ}{v : Val T τ} → 
         q , ignore (val v)                     , ρ ⟶e q , val U , ρ
  Let↦ : ∀{q ξ τ ρ}{v : Val T ξ}{e : Exp Δ Γ (ξ ∷ Ξ) T τ} → 
         q , Let (val v) e                      , ρ ⟶e q , subst-const v e , ρ
  Receive-Un⟶e : ∀{q τ ρ}{e₁ : Exp Δ Γ _ T τ}{e₂ : Exp Δ Γ _ T τ}{e₃ : Exp Δ Γ _ T τ}{e₄ : Exp Δ Γ _ T τ} → 
         ((Un , U) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val U) e₁ , ρ
  Receive-AR⟶e : ∀{q τ ρ x}{e₁ : Exp Δ Γ _ T τ}{e₂ : Exp Δ Γ _ T τ}{e₃ : Exp Δ Γ _ T τ}{e₄ : Exp Δ Γ _ T τ} → 
         ((AR , x) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val x) e₂ , ρ
  Receive-In⟶e : ∀{q τ ρ x}{e₁ : Exp Δ Γ _ T τ}{e₂ : Exp Δ Γ _ T τ}{e₃ : Exp Δ Γ _ T τ}{e₄ : Exp Δ Γ _ T τ} → 
         ((In , x) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val x) e₃ , ρ
  Receive-Bo⟶e : ∀{q τ ρ x}{e₁ : Exp Δ Γ _ T τ}{e₂ : Exp Δ Γ _ T τ}{e₃ : Exp Δ Γ _ T τ}{e₄ : Exp Δ Γ _ T τ} → 
         ((Bo , x) ∷ q) , receive e₁ e₂ e₃ e₄ , ρ ⟶e q , Let (val x) e₄ , ρ

data _⟶t_ {Δ T} : Task Δ T → Task Δ T → Set where
  exp⟶t : ∀{Γ τ φ e₀ e₀' q q' ρ ρ' cs}{e e' : Exp Δ Γ [] T τ}{E : E Δ Γ [] T φ τ} → 
    e ≡ E [ e₀ ] → q , e₀ , ρ ⟶e q' , e₀' , ρ' → e' ≡ E [ e₀' ] → 
    ⟨ q , e , ρ , cs ⟩ ⟶t ⟨ q' , e' , ρ' , cs ⟩
  call⟶t : ∀{Γ Λ τ q ρ cs φ args E}{e : Exp Δ Γ [] T τ}{f : Fun Δ Λ φ} → 
   (envF : EnvF Δ T) → (p : f （ args ） redex) → e ≡ E [ f （ args ） ] → 
    ⟨ q , e , ρ , cs ⟩ ⟶t ⟨ q , lkp-fun envF f , args-to-state f args p , < E / ρ > ∷ cs ⟩
  return⟶t : ∀{Γ Γ' φ τ q}{ρ : State T Γ'}{ρ' : State T Γ}{cs}{e : Exp Δ Γ [] T τ}{E : E Δ Γ [] T φ τ}{v : Val T φ} → 
    e ≡ E [ val v ] → 
    ⟨ q , val v , ρ , < E / ρ' > ∷ cs ⟩ ⟶t ⟨ q , e , ρ' , cs ⟩ 
  -- things handled in outer layers : spawn , spawng , yield , send

--
-- Layer 2 : group
--

data _↦_,_,_executable {Δ T} : ∀{n m o} → Vec (Task Δ T) n m → Vec (Task Δ T) n o → Task Δ T → Vec (Task Δ T) (suc o) m → Set where
  z-call-ex : ∀{Γ q ρ τ cs n}{e : Exp Δ Γ [] T τ}{c : Call Δ T}{ts : Vec (Task Δ T) zero n} →  
    (⟨ q , e , ρ , c ∷ cs ⟩ ∷ ts) ↦ ts , ⟨ q , e , ρ , c ∷ cs ⟩ , [] executable
  z-root-ex : ∀{Γ q ρ τ n}{ts : Vec (Task Δ T) zero n}{e : Exp Δ Γ [] T τ}{φ}{e' : Exp Δ Γ [] T φ}{E} → 
    e ≡ E [ e' ] → e' redex → 
    (⟨ q , e , ρ , [] ⟩ ∷ ts) ↦ ts , ⟨ q , e , ρ , [] ⟩ , [] executable
  s-ex : ∀{n m t}{ts : Vec (Task Δ T) zero n}{tasks₁ : Vec (Task Δ T) zero m}{tasks₂ : Vec (Task Δ T) (suc m) n}{task} →
    ts ↦ tasks₁ , task , tasks₂ executable →
    (t ∷ ts) ↦ tasks₁ , task , t ∷ tasks₂ executable

data _⟶g_ {Δ T} : ∀{n n'} → Group Δ T n → Group Δ T n' → Set where
  step⟶g : ∀{task task' n g g'}{m : Fin n}{E : GroupE Δ T n} → 
     task ⟶t task' → 
     g ≡G E [ task ] → g' ≡G E [ task' ] → 
     g ⟶g g'
  yield⟶g : ∀{Γ n m}{tasks₁ : Vec (Task Δ T) zero m}{tasks₂ : Vec (Task Δ T) (suc m) n}{tasks' task}{τ}{e e' : Exp Δ Γ [] T τ}{E₂ : E Δ Γ [] T Un τ}{q ρ cs}{E : GroupE Δ T n} → 
    e ≡ E₂ [ yield ] → e' ≡ E₂ [ skip ] → 
    group-busy tasks₁ task tasks₂ ≡G E [ ⟨ q , e , ρ , cs ⟩ ] → (group-idle tasks') ≡G E [ ⟨ q , e' , ρ , cs ⟩ ] → 
    group-busy tasks₁ task tasks₂ ⟶g group-idle tasks'
  schedule⟶g : ∀{n}{tasks : Vec (Task Δ T) zero n}{x : Fin n}{m}{tasks₁ : Vec (Task Δ T) zero m}{tasks₂ : Vec (Task Δ T) (suc m) n}{task} →
    tasks ↦ tasks₁ , task , tasks₂ executable →
    group-idle tasks ⟶g group-busy tasks₁ task tasks₂
  -- handle spawn here (?)

--
-- Layer 3 : configurations
--

open import Relation.Binary.PropositionalEquality renaming(_≡_ to _==_; [_] to ⟦_⟧)

spawng-extend : ∀{Δ Λ Γ σ S}{fun : Fun Δ Λ σ} → (args : ExpList Δ Γ [] S Λ) → (len : ℕ) → spawng fun args redex → spawng fun (extend-explist len args) redex
spawng-extend args len (spawng-redex p) = spawng-redex (values-extend args len p)

extend-CfgE : ∀{Δ l T idx}{S : Vec ℕ zero l} → (len : ℕ) → CfgE' Δ (_ , S) T idx → CfgE' Δ (suc _ , len ∷ S) T idx
extend-CfgE f (head-E x) = head-E (extend f x)
extend-CfgE f (tail-E x cfgE) = tail-E (extend-g f x) (extend-CfgE f cfgE)

extend-GroupE : ∀{Δ l n}{S : Vec ℕ zero l} → (len : ℕ) → GroupE Δ (_ , S) n → GroupE Δ (suc _ , len ∷ S) n
extend-GroupE f (group-E vec₁ vec₂) = group-E (Util.Vector.map (extend-t f) vec₁) (Util.Vector.map (extend-t f) vec₂)

max-taskid : ∀{t}{T : Vec ℕ zero t} → Val (suc t , 1 ∷ T) AR
max-taskid {T = T} = A {suc _ , 1 ∷ T} {lastidx (1 ∷ T)} (max-taskid' T)
  where max-taskid' : ∀{t} → (T : Vec ℕ zero t) → TaskID (suc t , 1 ∷ T) (lastidx (1 ∷ T))
        max-taskid' T rewrite down-lastidx {x = 1} T = zero

inc-task-grp : (T : TCtx) → Fin (proj₁ T) → TCtx
inc-task-grp (_ , T) idx = _ , (T [ idx ]≔ suc (lookup idx T))

infixr 5 _⟶c_

data _⟶c_ {Δ} : {R S : TCtx} → Cfg R → Cfg S → Set where
  step⟶c : ∀{S gid E}{cfg cfg' : Cfg S}{g g' : Group Δ S (lookup gid (proj₂ S))} →
    g ⟶g g' →
    cfg ≡C E [ g ] → cfg' ≡C E [ g' ] →
    cfg ⟶c cfg'

  send⟶c : ∀{Γ S gid}{cfg cfg' : Cfg S}{E₁}{g g' : Group Δ S (lookup gid (proj₂ S))}{E₂ q τ}{e e' : Exp Δ Γ [] S τ}{ρ cs φ}{msg : Val S φ}{E₃}{gid : Fin (proj₁ S)}{tid : TaskID S gid} →
    e   ≡  E₃ [ send (val (A tid)) (val msg) ] → e'   ≡  E₃ [ val msg ] → 
    g   ≡G E₂ [ ⟨ q , e , ρ , cs ⟩ ]           → g'   ≡G E₂ [ ⟨ q , e' , ρ , cs ⟩ ] → 
    cfg ≡C E₁ [ g ]                            → cfg' ≡C E₁ [ g' ] →
    cfg ⟶c deliver tid msg cfg'

  spawng⟶c : ∀{t}{idx : Fin t}{T : Vec ℕ zero t} → 
    ∀{Γ τ q ρ cs E} {e : Exp Δ Γ [] (t , T) τ}           {e' : Exp Δ Γ [] (suc _ , 1 ∷ T) τ} → 
    ∀{Eg}           {g : Group Δ (_ , T) (lookup idx T)} {g' : Group Δ (suc _ , 1 ∷ T) (lookup idx T)} →
    ∀{Ec}           {cfg : Cfg (_ , T)}                  {cfg' : Cfg' (suc _ , (suc zero) ∷ T) (_ , T) maxidx} → 

    ∀{Λ σ}{fun : Fun Δ Λ σ}{args : ExpList Δ Γ [] (_ , T) Λ} → 
    (envF : EnvF Δ (suc _ , (suc zero) ∷ T)) → (p : spawng fun args redex) → 

    e   ≡  E  [ spawng fun args ]    → e'   ≡  extend-E _ E     [ val max-taskid ] → 
    g   ≡G Eg [ ⟨ q , e , ρ , cs ⟩ ] → g'   ≡G extend-GroupE _ Eg [ ⟨ Data.List.map (extend-v' _) q , e' , extend-state _ ρ , Data.List.map (extend-call _ ) cs ⟩ ] → 
    cfg ≡C Ec [ g ]                  → cfg' ≡C extend-CfgE _ Ec   [ g' ] →
    cfg ⟶c group-idle [ ⟨ [] , lkp-fun envF fun , spawng-args-to-state fun (extend-explist _ args) (spawng-extend args _ p) , [] ⟩ ] ∷ cfg'

  spawn⟶c : ∀{T : TCtx}{gid}{cfg : Cfg T}{cfg' : Cfg' (_ , proj₂ T [ gid ]≔ suc (lookup gid (proj₂ T))) T maxidx} →
    ∀{g : Group Δ T (lookup gid (proj₂ T))}{g' : Group Δ (inc-task-grp T gid) (lookup gid (proj₂ T))}→ 
    ∀{Ec : CfgE' Δ T T gid}{Eg : GroupE Δ T (lookup gid (proj₂ T))}{Γ q τ ρ cs}{e : Exp Δ Γ [] T τ}  → 
    (envF : EnvF Δ T) → ∀{Λ σ}{fun : Fun Δ Λ σ}{args : ExpList Δ Γ [] T Λ}{E : E Δ Γ [] T AR τ} → 
    {e' : Exp Δ Γ [] (inc-task-grp T gid) τ} → (p : spawn fun args redex) → 

     e ≡  E  [ spawn fun args ]     →   e' ≡ extendt-E [] (proj₂ T) gid E [ val (A (subst Fin (lookup-suc-eq gid (proj₂ T)) maxidx)) ] → 
     g ≡G Eg [ ⟨ q , e , ρ , cs ⟩ ] →   g' ≡G extendt-GroupE [] (proj₂ T) gid Eg [ ⟨ Data.List.map (extendt-val' [] (proj₂ T) gid) q , e' , extendt-state [] (proj₂ T) gid ρ , Data.List.map (extendt-call [] (proj₂ T) gid) cs ⟩ ] →
   cfg ≡C Ec [ g ]                  → cfg' ≡C extendt-CfgE [] (proj₂ T) gid Ec [ g' ] → 
   cfg ⟶c extendt-Cfg' [] (proj₂ T) gid ⟨ [] , lkp-fun envF fun , spawn-args-to-state fun args p , [] ⟩ cfg'
