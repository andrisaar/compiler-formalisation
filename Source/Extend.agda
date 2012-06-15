module Source.Extend where

open import Data.Fin
open import Data.Nat
open import Data.List renaming (map to mapl)
open import Data.Product hiding (map)
open import Data.Maybe

open import Source.Syntax
open import Source.EvalCtx

open import Util.Vector

open import Relation.Binary.PropositionalEquality renaming ([_] to ⟦_⟧)
{-
  -- rename to Extend
record Map (T T' : TCtx) : Set where
  field lmap : Fin (proj₁ T) → Fin (proj₁ T')
        emap : (gid : Fin (proj₁ T)) → Fin (lookup gid (proj₂ T)) → Fin (lookup (lmap gid) (proj₂ T'))

-- length of T is leq than T'
-- 
        lmap-suc : ∀{m} → suc m ≡ proj₁ T → ∃ λ n' → suc n' ≡ proj₁ T'
        lmap-zero : ∀{m} → (p : suc m ≡ proj₁ T) → lmap (subst Fin p zero) ≡ subst Fin (proj₂ (lmap-suc p)) zero
--lmap (subst Fin p (suc x)) ≡ {!!}
        -- lmap (suc x) ≡ suc (lmap x)
--        lmap-suc : ∀{n : ℕ}{x : Fin n} → (p : (_≅_ {A = ℕ} (suc n) (proj₁ T))) → _≅_ {A = Fin (proj₁ T')} (lmap (subst' Fin p (suc x))) {B = {!Fin n!}} (suc (lmap x))
-- 

subst-zero' : ∀{m n : ℕ} → (p : suc m ≡ n) → inject₁ (subst Fin p zero) ≡ zero
subst-zero' refl = refl

NewGroup : ∀{n}{T : Vec ℕ zero n} → (len : ℕ) → Map (_ , T) (suc _ , len ∷ T)
NewGroup {n} len = record {
  lmap = inject₁;
  emap = emap';
  lmap-suc = lmap-suc';
  lmap-zero = subst-zero'
  }
  where emap' : ∀{n T len} → (gid : Fin n) → Fin (lookup gid T) → Fin (lookup (inject₁ gid) (len ∷ T))
        emap' gid x rewrite down-inject gid = x
        lmap-suc' : {m : ℕ} → suc m ≡ n → ∃ λ n' → suc n' ≡ (suc n)
        lmap-suc' {m} _ = n , refl

NewTask : ∀{n}{T : Vec ℕ zero n} → (gid : Fin n) → Map (_ , T) (_ , T [ gid ]≔ suc (lookup gid T))
NewTask {n} {T} gid = record {
  lmap = λ x → x;
  emap = emap' {n} {T} gid;
  lmap-suc = lmap-suc';
  lmap-zero = λ _ → refl
  }
  where lmap-suc' : {m : ℕ} → suc m ≡ n → ∃ λ n' → suc n' ≡ n
        lmap-suc' {m} p = m , p
        emap' : ∀{n T} → (gid : Fin n) → (gid₂ : Fin n) → Fin (lookup gid₂ T) → Fin (lookup gid₂ (T [ gid ]≔ suc (lookup gid T)))
        emap' {zero}     {[]}     ()       ()       _
        emap' {suc zero} {_ ∷ []} zero     zero     x = inject₁ x
        emap' {suc zero} {_ ∷ []} zero     (suc ()) _
        emap' {suc zero} {_ ∷ []} (suc ()) _        _
        emap' {suc (suc _)} {_ ∷ T} gid₁ gid₂ x with down (suc _) gid₁
        emap' {suc (suc n)} {_ ∷ T} gid₁ gid₂ x | just _ with down (suc _) gid₂
        emap' {suc (suc n)} {_ ∷ T} gid₁ gid₂ x | just gid₁' | just gid₂' = emap' {T = T} gid₁' gid₂' x
        emap' {suc (suc n)} {_ ∷ T} gid₁ gid₂ x | just _     | nothing    = x
        emap' {suc (suc n)} {_ ∷ T} gid₁ gid₂ x | nothing with down (suc _) gid₂
        emap' {suc (suc n)} {_ ∷ T} gid₁ gid₂ x | nothing    | just _     = x
        emap' {suc (suc n)} {_ ∷ T} gid₁ gid₂ x | nothing    | nothing    = inject₁ x



extend-val : ∀{T T' τ} → (f : Map T T') → Val T τ → Val T' τ
extend-val f U = U
extend-val {T} {T'} f (A {n} x) = A {T'} {Map.lmap f n} (Map.emap f n x)
extend-val f (N x) = N x
extend-val f (B x) = B x

extend-exp : ∀{Δ Γ Ξ τ S S'} → (f : Map S S') → Exp Δ Γ Ξ S τ → Exp Δ Γ Ξ S' τ

extend-explist : ∀{Δ Γ Ξ τ S S'} → (f : Map S S') → ExpList Δ Γ Ξ S τ → ExpList Δ Γ Ξ S' τ
extend-explist f [] = []
extend-explist f (x ∷ el) = extend-exp f x ∷ extend-explist f el

extend-exp f (var x) = var x
extend-exp f (val x) = val (extend-val f x)
extend-exp f (const x) = const x
extend-exp f (e ≐ e₁) = extend-exp f e ≐ extend-exp f e₁
extend-exp f (¬ e) = ¬ extend-exp f e
extend-exp f (e ∔ e₁) = extend-exp f e ∔ extend-exp f e₁
extend-exp f (e ⊻ e₁) = extend-exp f e ⊻ extend-exp f e₁
extend-exp f avail = avail
extend-exp f (fun （ args ）) = fun （ extend-explist f args ）
extend-exp f (spawn fun args) = spawn fun (extend-explist f args)
extend-exp f (spawng fun args) = spawng fun (extend-explist f args)
extend-exp f yield = yield
extend-exp f (x ≔ e) = x ≔ extend-exp f e
extend-exp f skip = skip
extend-exp f (e , e₁) = extend-exp f e , extend-exp f e₁
extend-exp f (If e then e₁ else e₂) = If (extend-exp f e) then (extend-exp f e₁) else (extend-exp f e₂)
extend-exp f (While e do e₁) = While (extend-exp f e) do (extend-exp f e₁)
extend-exp f (send e e₁) = send (extend-exp f e) (extend-exp f e₁)
extend-exp f (receive e e₁ e₂ e₃) = receive (extend-exp f e) (extend-exp f e₁) (extend-exp f e₂) (extend-exp f e₃)
extend-exp f (ignore e) = ignore (extend-exp f e)
extend-exp f (Let e e₁) = Let (extend-exp f e) (extend-exp f e₁)

extend-state : ∀{Γ S S'} → (f : Map S S') → State S Γ → State S' Γ
extend-state f [] = []
extend-state f (x ∷ state) = extend-val f x ∷ extend-state f state

extend-E : ∀{Δ Γ Ξ φ τ S S'} → (f : Map S S') → E Δ Γ Ξ S φ τ → E Δ Γ Ξ S' φ τ

extend-FunE : ∀{Δ Γ Ξ Λ S S'} → (f : Map S S') → FunE Δ Γ Ξ S Λ → FunE Δ Γ Ξ S' Λ
extend-FunE f empty = empty
extend-FunE f (val x funE) = val (extend-val f x) (extend-FunE f funE)
extend-FunE f (exp x x₁) = exp (extend-E f x) (extend-explist f x₁)

extend-E f □ = □
extend-E f (¬-E e) = ¬-E (extend-E f e)
extend-E f (∨l-E e x) = ∨l-E (extend-E f e) (extend-exp f x)
extend-E f (∨r-E x e) = ∨r-E (extend-val f x) (extend-E f e)
extend-E f (=l-E e x) = =l-E (extend-E f e) (extend-exp f x)
extend-E f (=r-E x e) = =r-E (extend-val f x) (extend-E f e)
extend-E f (+l-E e x) = +l-E (extend-E f e) (extend-exp f x)
extend-E f (+r-E x e) = +r-E (extend-val f x) (extend-E f e)
extend-E f (call-E fun x) = call-E fun (extend-FunE f x)
extend-E f (spawn-E fun x) = spawn-E fun (extend-FunE f x)
extend-E f (spawng-E fun x) = spawng-E fun (extend-FunE f x)
extend-E f (≔-E v e) = ≔-E v (extend-E f e)
extend-E f (,-E e x) = ,-E (extend-E f e) (extend-exp f x)
extend-E f (if-E e x x₁) = if-E (extend-E f e) (extend-exp f x) (extend-exp f x₁)
extend-E f (ignore-E e) = ignore-E (extend-E f e)
extend-E f (sendl-E e x) = sendl-E (extend-E f e) (extend-exp f x)
extend-E f (sendr-E x e) = sendr-E (extend-val f x) (extend-E f e)
extend-E f (Let-E e x) = Let-E (extend-E f e) (extend-exp f x)

extend-call : ∀{Δ S S'} → (f : Map S S') → Call Δ S → Call Δ S'
extend-call f < E / state > = < extend-E f E / extend-state f state >

extend-v' : ∀{S S'} → (f : Map S S') → (∃ λ τ → Val S τ) → (∃ λ τ → Val S' τ)
extend-v' f (proj₁ , proj₂) = proj₁ , extend-val f proj₂

extend-t : ∀{Δ S S'} → (f : Map S S') → Task Δ S → Task Δ S'
extend-t f ⟨ q , e , ρ , cs ⟩ = ⟨ mapl (extend-v' f) q , extend-exp f e , extend-state f ρ , mapl (extend-call f) cs ⟩

extend-g : ∀{Δ S S' n} → (f : Map S S') → Group Δ S n → Group Δ S' n
extend-g f (group-busy tasks₁ task tasks₂) = group-busy (map (extend-t f) tasks₁) (extend-t f task) (map (extend-t f) tasks₂)
extend-g f (group-idle tasks) = group-idle (map (extend-t f) tasks)

extend : ∀{S S' T idx} → (f : Map S S') → Cfg' S T idx → Cfg' S' T idx
extend f [] = []
extend f (x ∷ cfg) = extend-g f x ∷ extend f cfg

values-extend : ∀{Γ Δ Ξ S S' Λ}{f : Map S S'} → (el : ExpList Γ Δ Ξ S Λ) → el values → (extend-explist f el) values
values-extend .[] []-values = []-values
values-extend .(val v ∷ l) (∷-values v l p) = ∷-values (extend-val _ v) (extend-explist _ l) (values-extend l p)

-}

extend-val : ∀{l}{S : Vec ℕ zero l}{τ} → (len : ℕ) → Val (_ , S) τ → Val (suc _ , len ∷ S) τ
extend-val len U = U
extend-val {S = S} len (A {n} x) = A (subst Fin (sym (lookup-extend {x = lookup n S} n refl)) x)
extend-val len (N x) = N x
extend-val len (B x) = B x

extend-exp : ∀{Δ Γ Ξ τ l}{S : Vec ℕ zero l} → (len : ℕ) → Exp Δ Γ Ξ (_ , S) τ → Exp Δ Γ Ξ (suc _ , len ∷ S) τ

extend-explist : ∀{Δ Γ Ξ τ l}{S : Vec ℕ zero l} → (len : ℕ) → ExpList Δ Γ Ξ (_ , S) τ → ExpList Δ Γ Ξ (suc _ , len ∷ S) τ
extend-explist len [] = []
extend-explist len (x ∷ el) = extend-exp len x ∷ extend-explist len el

values-extend : ∀{Γ Δ Ξ l τ}{S : Vec ℕ zero l} → (v : ExpList Γ Δ Ξ (_ , S) τ) → (len : ℕ) → v values → (extend-explist len v) values

extend-exp len (var x) = var x
extend-exp len (val x) = val (extend-val len x)
extend-exp len (const x) = const x
extend-exp len (e ≐ e₁) = extend-exp len e ≐ extend-exp len e₁
extend-exp len (¬ e) = ¬ extend-exp len e
extend-exp len (e ∔ e₁) = extend-exp len e ∔ extend-exp len e₁
extend-exp len (e ⊻ e₁) = extend-exp len e ⊻ extend-exp len e₁
extend-exp len avail = avail
extend-exp len (fun （ args ）) = fun （ extend-explist len args ）
extend-exp len (spawn fun args) = spawn fun (extend-explist len args)
extend-exp len (spawng fun args) = spawng fun (extend-explist len args)
extend-exp len yield = yield
extend-exp len (x ≔ e) = x ≔ extend-exp len e
extend-exp len skip = skip
extend-exp len (e , e₁) = extend-exp len e , extend-exp len e₁
extend-exp len (If e then e₁ else e₂) = If (extend-exp len e) then (extend-exp len e₁) else (extend-exp len e₂)
extend-exp len (While e do e₁) = While (extend-exp len e) do (extend-exp len e₁)
extend-exp len (send e e₁) = send (extend-exp len e) (extend-exp len e₁)
extend-exp len (receive e e₁ e₂ e₃) = receive (extend-exp len e) (extend-exp len e₁) (extend-exp len e₂) (extend-exp len e₃)
extend-exp len (ignore e) = ignore (extend-exp len e)
extend-exp len (Let e e₁) = Let (extend-exp len e) (extend-exp len e₁)

values-extend .[] len []-values = []-values
values-extend .(val v₁ ∷ v) len (∷-values v₁ v p) = ∷-values (extend-val len v₁) (extend-explist len v) (values-extend v len p)

extend-state : ∀{Γ l}{S : Vec ℕ zero l} → (len : ℕ) → State (l , S) Γ → State (suc _ , len ∷ S) Γ
extend-state len [] = []
extend-state len (x ∷ state) = extend-val len x ∷ extend-state len state

extend-E : ∀{Δ Γ Ξ l φ τ}{S : Vec ℕ zero l} → (len : ℕ) → E Δ Γ Ξ (_ , S) φ τ → E Δ Γ Ξ (suc _ , len ∷ S) φ τ

extend-FunE : ∀{Δ Γ Ξ Λ l}{S : Vec ℕ zero l} → (len : ℕ) → FunE Δ Γ Ξ (_ , S) Λ → FunE Δ Γ Ξ (suc _ , len ∷ S) Λ
extend-FunE len empty = empty
extend-FunE len (val x funE) = val (extend-val len x) (extend-FunE len funE)
extend-FunE len (exp x x₁) = exp (extend-E len x) (extend-explist len x₁)

extend-E len □ = □
extend-E len (¬-E e) = ¬-E (extend-E len e)
extend-E len (∨l-E e x) = ∨l-E (extend-E len e) (extend-exp len x)
extend-E len (∨r-E x e) = ∨r-E (extend-val len x) (extend-E len e)
extend-E len (=l-E e x) = =l-E (extend-E len e) (extend-exp len x)
extend-E len (=r-E x e) = =r-E (extend-val len x) (extend-E len e)
extend-E len (+l-E e x) = +l-E (extend-E len e) (extend-exp len x)
extend-E len (+r-E x e) = +r-E (extend-val len x) (extend-E len e)
extend-E len (call-E f x) = call-E f (extend-FunE len x)
extend-E len (spawn-E f x) = spawn-E f (extend-FunE len x)
extend-E len (spawng-E f x) = spawng-E f (extend-FunE len x)
extend-E len (≔-E v e) = ≔-E v (extend-E len e)
extend-E len (,-E e x) = ,-E (extend-E len e) (extend-exp len x)
extend-E len (if-E e x x₁) = if-E (extend-E len e) (extend-exp len x) (extend-exp len x₁)
extend-E len (ignore-E e) = ignore-E (extend-E len e)
extend-E len (sendl-E e x) = sendl-E (extend-E len e) (extend-exp len x)
extend-E len (sendr-E x e) = sendr-E (extend-val len x) (extend-E len e)
extend-E len (Let-E e x) = Let-E (extend-E len e) (extend-exp len x)

extend-call : ∀{Δ l}{S : Vec ℕ zero l} → (len : ℕ) → Call Δ (l , S) → Call Δ (suc _ , len ∷ S)
extend-call len < E / state > = < extend-E len E / extend-state len state >

extend-v' : ∀{l}{S : Vec ℕ zero l} → (len : ℕ) → (∃ λ τ → Val (_ , S) τ) → (∃ λ τ → Val (suc _ , len ∷ S) τ)
extend-v' len (proj₁ , proj₂) = proj₁ , extend-val len proj₂

extend-t : ∀{Δ l}{S : Vec ℕ zero l} → (len : ℕ) → Task Δ (_ , S) → Task Δ (suc _ , len ∷ S)
extend-t len ⟨ q , e , ρ , cs ⟩ = ⟨ Data.List.map (extend-v' len) q , extend-exp len e , extend-state len ρ , Data.List.map (extend-call len) cs ⟩

extend-g : ∀{Δ l}{S : Vec ℕ zero l}{n} → (len : ℕ) → Group Δ (_ , S) n → Group Δ (suc _ , (len ∷ S)) n
extend-g len (group-busy tasks₁ task tasks₂) = group-busy (Util.Vector.map (extend-t len) tasks₁) (extend-t len task) (Util.Vector.map (extend-t len) tasks₂)
extend-g len (group-idle tasks) = group-idle (Util.Vector.map (extend-t len) tasks)

extend : ∀{Δ S T idx} → (len : ℕ) → Cfg' {Δ} S T idx → Cfg' {Δ} (suc _ , (len ∷ proj₂ S)) T idx
extend _   []        = []
extend len (x ∷ cfg) = extend-g len x ∷ extend len cfg


--extend-call : ∀{Δ l}{T : Vec ℕ zero l}{len} → Call Δ (_ , T) → Call Δ (suc _ , len ∷ T)
--extend-call = ?

