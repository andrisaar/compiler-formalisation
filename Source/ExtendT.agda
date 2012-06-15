module Source.ExtendT where

open import Data.Nat
open import Data.Fin
open import Data.Product hiding (map)
open import Data.List hiding (_++_; _∷ʳ_; [_]) renaming (map to lmap)
open import Data.Maybe

open import Source.Syntax
open import Source.EvalCtx
--open import Source.Extend
open import Util.Vector

open import Relation.Binary.PropositionalEquality renaming ([_] to ⟦_⟧)

emap : ∀{n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → (gid₂ : Fin m) → Fin (lookup gid₂ (S ++ T)) → Fin (lookup gid₂ (S ++ T [ gid ]≔ suc (lookup gid T)))
emap [] [] () () _
emap [] (x ∷ T) gid₁ gid₂ x₁ with down _ gid₁ | down _ gid₂ | inspect (down _) gid₂
... | just gid₁' | just gid₂' | ⟦ eq ⟧ rewrite eq = emap [] T gid₁' gid₂' x₁
... | just gid₁' | nothing    | ⟦ eq ⟧ rewrite eq = x₁
... | nothing    | just gid₂' | ⟦ eq ⟧ rewrite eq = x₁
... | nothing    | nothing    | ⟦ eq ⟧ rewrite eq = inject₁ x₁
emap (x ∷ S) T gid₁ gid₂ x₁ with down _ gid₂
... | just gid₂' = emap S T gid₁ gid₂' x₁
... | nothing = x₁

extendt-val : ∀{n m τ} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → Val (_ , S ++ T) τ → Val (_ , S ++ T [ gid ]≔ suc (lookup gid T)) τ
extendt-val S T idx U = U
extendt-val S T idx (A {n} x) = A (emap S T idx n x)
extendt-val S T idx (N x) = N x
extendt-val S T idx (B x) = B x

extendt-Fin : ∀{n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → (n : Fin m) → Fin (lookup n (A ++ x ∷ B ++ C)) → Fin (lookup n (A ++ suc x ∷ B ++ C))
extendt-Fin {n = m} [] B' C' n v with down m n
... | nothing = inject₁ v
... | just n' = v
extendt-Fin {m = suc m} (a ∷ A') B' C' n v with down m n
... | nothing = v
... | just n' = extendt-Fin A' B' C' n' v

extendt-val₂ : ∀{τ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → Val (_ , A ++ x ∷ B ++ C) τ → Val (_ , A ++ suc x ∷ B ++ C) τ
extendt-val₂ A' B' C' U = U
extendt-val₂ A' B' C' (A {n} x₁) = A {n = n} (extendt-Fin A' B' C' n x₁)
extendt-val₂ A' B' C' (N x₁) = N x₁
extendt-val₂ A' B' C' (B x₁) = B x₁

extendt-val₂' : ∀{n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → (∃ λ τ → Val (_ , A ++ x ∷ B ++ C) τ) → (∃ λ τ → Val (_ , A ++ suc x ∷ B ++ C) τ)
extendt-val₂' A' B' C' (proj₁ , proj₂) = proj₁ , extendt-val₂ A' B' C' proj₂

extendt-val' : ∀{n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → (∃ λ τ → Val (_ , S ++ T) τ) → (∃ λ τ → Val (_ , S ++ T [ gid ]≔ suc (lookup gid T)) τ)
extendt-val' S T idx (proj₁ , proj₂) = proj₁ , extendt-val S T idx proj₂

extendt-exp₂ : ∀{Δ Γ Ξ τ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → Exp Δ Γ Ξ (_ , A ++ x ∷ B ++ C) τ → Exp Δ Γ Ξ (_ , A ++ suc x ∷ B ++ C) τ

extendt-explist₂ : ∀{Δ Γ Ξ τ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → ExpList Δ Γ Ξ (_ , A ++ x ∷ B ++ C) τ → ExpList Δ Γ Ξ (_ , A ++ suc x ∷ B ++ C) τ
extendt-explist₂ _ _ _ [] = []
extendt-explist₂ A' B' C' (x ∷ el) = extendt-exp₂ A' B' C' x ∷ extendt-explist₂ A' B' C' el

extendt-exp₂ A' B' C' (var x) = var x
extendt-exp₂ A' B' C' (val x) = val (extendt-val₂ A' B' C' x)
extendt-exp₂ A' B' C' (const x) = const x
extendt-exp₂ A' B' C' (e ≐ e₁) = extendt-exp₂ A' B' C' e ≐ extendt-exp₂ A' B' C' e₁
extendt-exp₂ A' B' C' (¬ e) = ¬ extendt-exp₂ A' B' C' e
extendt-exp₂ A' B' C' (e ∔ e₁) = extendt-exp₂ A' B' C' e ∔ extendt-exp₂ A' B' C' e₁
extendt-exp₂ A' B' C' (e ⊻ e₁) = extendt-exp₂ A' B' C' e ⊻ extendt-exp₂ A' B' C' e₁
extendt-exp₂ A' B' C' avail = avail
extendt-exp₂ A' B' C' (fun （ args ）) = fun （ extendt-explist₂ A' B' C' args ）
extendt-exp₂ A' B' C' (spawn fun args) = spawn fun (extendt-explist₂ A' B' C' args)
extendt-exp₂ A' B' C' (spawng fun args) = spawng fun (extendt-explist₂ A' B' C' args)
extendt-exp₂ A' B' C' yield = yield
extendt-exp₂ A' B' C' (x ≔ e) = x ≔ extendt-exp₂ A' B' C' e
extendt-exp₂ A' B' C' skip = skip
extendt-exp₂ A' B' C' (e , e₁) = extendt-exp₂ A' B' C' e , extendt-exp₂ A' B' C' e₁
extendt-exp₂ A' B' C' (If e then e₁ else e₂) = If extendt-exp₂ A' B' C' e then extendt-exp₂ A' B' C' e₁ else extendt-exp₂ A' B' C' e₂
extendt-exp₂ A' B' C' (While e do e₁) = While extendt-exp₂ A' B' C' e do extendt-exp₂ A' B' C' e₁
extendt-exp₂ A' B' C' (send e e₁) = send (extendt-exp₂ A' B' C' e) (extendt-exp₂ A' B' C' e₁)
extendt-exp₂ A' B' C' (receive e e₁ e₂ e₃) = receive (extendt-exp₂ A' B' C' e) (extendt-exp₂ A' B' C' e₁) (extendt-exp₂ A' B' C' e₂) (extendt-exp₂ A' B' C' e₃)
extendt-exp₂ A' B' C' (ignore e) = ignore (extendt-exp₂ A' B' C' e)
extendt-exp₂ A' B' C' (Let e e₁) = Let (extendt-exp₂ A' B' C' e) (extendt-exp₂ A' B' C' e₁)

extendt-exp : ∀{Δ Γ Ξ τ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → Exp Δ Γ Ξ (_ , S ++ T) τ → Exp Δ Γ Ξ (_ , S ++ T [ gid ]≔ suc (lookup gid T)) τ

extendt-explist : ∀{Δ Γ Ξ τ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → ExpList Δ Γ Ξ (_ , S ++ T) τ → ExpList Δ Γ Ξ (_ , S ++ T [ gid ]≔ suc (lookup gid T)) τ
extendt-explist S T idx [] = []
extendt-explist S T idx (x ∷ el) = extendt-exp S T idx x ∷ extendt-explist S T idx el

extendt-values : ∀{Γ Δ Ξ n m τ} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → (v : ExpList Γ Δ Ξ (_ , S ++ T) τ) → v values → (extendt-explist S T gid v) values

extendt-exp S T idx (var x) = var x
extendt-exp S T idx (val x) = val (extendt-val S T idx x)
extendt-exp S T idx (const x) = const x
extendt-exp S T idx (e ≐ e₁) = extendt-exp S T idx e ≐ extendt-exp S T idx e₁
extendt-exp S T idx (¬ e) = ¬ extendt-exp S T idx e
extendt-exp S T idx (e ∔ e₁) = extendt-exp S T idx e ∔ extendt-exp S T idx e₁
extendt-exp S T idx (e ⊻ e₁) = extendt-exp S T idx e ⊻ extendt-exp S T idx e₁
extendt-exp S T idx avail = avail
extendt-exp S T idx (f （ args ）) = f （ extendt-explist S T idx args ）
extendt-exp S T idx (spawn f args) = spawn f (extendt-explist S T idx args)
extendt-exp S T idx (spawng f args) = spawng f (extendt-explist S T idx args)
extendt-exp S T idx yield = yield
extendt-exp S T idx (x ≔ e) = x ≔ extendt-exp S T idx e
extendt-exp S T idx skip = skip
extendt-exp S T idx (e , e₁) = extendt-exp S T idx e , extendt-exp S T idx e₁
extendt-exp S T idx (If e then e₁ else e₂) = If extendt-exp S T idx e then extendt-exp S T idx e₁ else extendt-exp S T idx e₂
extendt-exp S T idx (While e do e₁) = While extendt-exp S T idx e do extendt-exp S T idx e₁
extendt-exp S T idx (send e e₁) = send (extendt-exp S T idx e) (extendt-exp S T idx e₁)
extendt-exp S T idx (receive e e₁ e₂ e₃) = receive (extendt-exp S T idx e) (extendt-exp S T idx e₁) (extendt-exp S T idx e₂) (extendt-exp S T idx e₃)
extendt-exp S T idx (ignore e) = ignore (extendt-exp S T idx e)
extendt-exp S T idx (Let e e₁) = Let (extendt-exp S T idx e) (extendt-exp S T idx e₁)

extendt-values S T gid .[] []-values = []-values
extendt-values S T gid .(val v ∷ l) (∷-values v l p) = ∷-values (extendt-val S T gid v) (extendt-explist S T gid l) (extendt-values S T gid l p)

extendt-E : ∀{Δ Γ Ξ σ τ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → E Δ Γ Ξ (_ , S ++ T) σ τ → E Δ Γ Ξ (_ , S ++ T [ gid ]≔ suc (lookup gid T)) σ τ

extendt-FunE : ∀{Δ Γ Ξ Λ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → FunE Δ Γ Ξ (_ , S ++ T) Λ → FunE Δ Γ Ξ (_ , S ++ T [ gid ]≔ suc (lookup gid T)) Λ
extendt-FunE S T idx empty = empty
extendt-FunE S T idx (val x funE) = val (extendt-val S T idx x) (extendt-FunE S T idx funE)
extendt-FunE S T idx (exp x x₁) = exp (extendt-E S T idx x) (extendt-explist S T idx x₁)

extendt-E S T idx □ = □
extendt-E S T idx (¬-E E) = ¬-E (extendt-E S T idx E)
extendt-E S T idx (∨l-E E x) = ∨l-E (extendt-E S T idx E) (extendt-exp S T idx x)
extendt-E S T idx (∨r-E x E) = ∨r-E (extendt-val S T idx x) (extendt-E S T idx E)
extendt-E S T idx (=l-E E x) = =l-E (extendt-E S T idx E) (extendt-exp S T idx x)
extendt-E S T idx (=r-E x E) = =r-E (extendt-val S T idx x) (extendt-E S T idx E)
extendt-E S T idx (+l-E E x) = +l-E (extendt-E S T idx E) (extendt-exp S T idx x)
extendt-E S T idx (+r-E x E) = +r-E (extendt-val S T idx x) (extendt-E S T idx E)
extendt-E S T idx (call-E f x) = call-E f (extendt-FunE S T idx x)
extendt-E S T idx (spawn-E f x) = spawn-E f (extendt-FunE S T idx x)
extendt-E S T idx (spawng-E f x) = spawng-E f (extendt-FunE S T idx x)
extendt-E S T idx (≔-E v E) = ≔-E v (extendt-E S T idx E)
extendt-E S T idx (,-E E x) = ,-E (extendt-E S T idx E) (extendt-exp S T idx x)
extendt-E S T idx (if-E E x x₁) = if-E (extendt-E S T idx E) (extendt-exp S T idx x) (extendt-exp S T idx x₁)
extendt-E S T idx (ignore-E E) = ignore-E (extendt-E S T idx E)
extendt-E S T idx (sendl-E E x) = sendl-E (extendt-E S T idx E) (extendt-exp S T idx x)
extendt-E S T idx (sendr-E x E) = sendr-E (extendt-val S T idx x) (extendt-E S T idx E)
extendt-E S T idx (Let-E E x) = Let-E (extendt-E S T idx E) (extendt-exp S T idx x)

extendt-E₂ : ∀{Δ Γ Ξ σ τ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → E Δ Γ Ξ (_ , A ++ x ∷ B ++ C) σ τ → E Δ Γ Ξ (_ , A ++ suc x ∷ B ++ C) σ τ

extendt-FunE₂ : ∀{Δ Γ Ξ Λ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → FunE Δ Γ Ξ (_ , A ++ x ∷ B ++ C) Λ → FunE Δ Γ Ξ (_ , A ++ suc x ∷ B ++ C) Λ
extendt-FunE₂ A' B' C' empty = empty
extendt-FunE₂ A' B' C' (val x₁ e) = val (extendt-val₂ A' B' C' x₁) (extendt-FunE₂ A' B' C' e)
extendt-FunE₂ A' B' C' (exp x₁ x₂) = exp (extendt-E₂ A' B' C' x₁) (extendt-explist₂ A' B' C' x₂)

extendt-E₂ A' B' C' □ = □
extendt-E₂ A' B' C' (¬-E e) = ¬-E (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (∨l-E e x₁) = ∨l-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁)
extendt-E₂ A' B' C' (∨r-E x₁ e) = ∨r-E (extendt-val₂ A' B' C' x₁) (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (=l-E e x₁) = =l-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁)
extendt-E₂ A' B' C' (=r-E x₁ e) = =r-E (extendt-val₂ A' B' C' x₁) (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (+l-E e x₁) = +l-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁)
extendt-E₂ A' B' C' (+r-E x₁ e) = +r-E (extendt-val₂ A' B' C' x₁) (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (call-E f x₁) = call-E f (extendt-FunE₂ A' B' C' x₁)
extendt-E₂ A' B' C' (spawn-E f x₁) = spawn-E f (extendt-FunE₂ A' B' C' x₁)
extendt-E₂ A' B' C' (spawng-E f x₁) = spawng-E f (extendt-FunE₂ A' B' C' x₁)
extendt-E₂ A' B' C' (≔-E v e) = ≔-E v (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (,-E e x₁) = ,-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁)
extendt-E₂ A' B' C' (if-E e x₁ x₂) = if-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁) (extendt-exp₂ A' B' C' x₂)
extendt-E₂ A' B' C' (ignore-E e) = ignore-E (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (sendl-E e x₁) = sendl-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁)
extendt-E₂ A' B' C' (sendr-E x₁ e) = sendr-E (extendt-val₂ A' B' C' x₁) (extendt-E₂ A' B' C' e)
extendt-E₂ A' B' C' (Let-E e x₁) = Let-E (extendt-E₂ A' B' C' e) (extendt-exp₂ A' B' C' x₁)

extendt-state : ∀{Γ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (idx : Fin n) → State (_ , S ++ T) Γ → State (_ , S ++ T [ idx ]≔ suc (lookup idx T)) Γ
extendt-state S T idx [] = []
extendt-state S T idx (x ∷ state) = extendt-val S T idx x ∷ extendt-state S T idx state

extendt-state₂ : ∀{Γ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → State (_ , A ++ x ∷ B ++ C) Γ → State (_ , A ++ suc x ∷ B ++ C) Γ
extendt-state₂ A' B' C' []      = []
extendt-state₂ A' B' C' (v ∷ ρ) = extendt-val₂ A' B' C' v ∷ extendt-state₂ A' B' C' ρ

extendt-call : ∀{Δ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (idx : Fin n) → Call Δ (_ , S ++ T) → Call Δ (_ , S ++ T [ idx ]≔ suc (lookup idx T))
extendt-call S T idx < x / x₁ > = < extendt-E S T idx x / extendt-state S T idx x₁ >

extendt-call₂ : ∀{Δ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → Call Δ (_ , A ++ x ∷ B ++ C) → Call Δ (_ , A ++ suc x ∷ B ++ C)
extendt-call₂ A' B' C' < E / ρ > = < extendt-E₂ A' B' C' E / extendt-state₂ A' B' C' ρ  >

extendt-task : ∀{Δ n m} → (S : Vec ℕ zero n) → (T : Vec ℕ n m) → (idx : Fin n) → Task Δ (_ , T ++ S) → Task Δ (_ , T ++ S [ idx ]≔ suc (lookup idx S))
extendt-task S T idx ⟨ q , e , ρ , cs ⟩ = ⟨ lmap (extendt-val' T S idx) q , extendt-exp T S idx e , extendt-state T S idx ρ , lmap (extendt-call T S idx) cs ⟩

extendt-task₂ : ∀{Δ n m o x} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → Task Δ (_ , A ++ x ∷ B ++ C) → Task Δ (_ , A ++ suc x ∷ B ++ C)
extendt-task₂ A' B' C' ⟨ q , e , ρ , cs ⟩ = ⟨ lmap (extendt-val₂' A' B' C') q , extendt-exp₂ A' B' C' e , extendt-state₂ A' B' C' ρ , lmap (extendt-call₂ A' B' C') cs ⟩

extendt-GroupE : ∀{Δ m n o} → (S : Vec ℕ n o) → (T : Vec ℕ zero n) → (idx : Fin n) → GroupE Δ (_ , S ++ T) m → GroupE Δ (_ , S ++ T [ idx ]≔ suc (lookup idx T)) m
extendt-GroupE S T idx (group-E x x₁) = group-E (map (extendt-task T S idx) x) (map (extendt-task T S idx) x₁)

extendt-group : ∀{Δ m n l} → (S : Vec ℕ zero n) → (T : Vec ℕ n m) → (idx : Fin n) → Group Δ (_ , T ++ S) l → Group Δ (_ , T ++ S [ idx ]≔ suc (lookup idx S)) l
extendt-group S T idx (group-busy x x₁ x₂) = group-busy (map (extendt-task S T idx) x) (extendt-task S T idx x₁) (map (extendt-task S T idx) x₂)
extendt-group S T idx (group-idle x) = group-idle (map (extendt-task S T idx) x)

extendt-group₂ : ∀{Δ n m o x len} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → Group Δ (_ , A ++ x ∷ B ++ C) len → Group Δ (_ , A ++ suc x ∷ B ++ C) len
extendt-group₂ A' B' C' (group-busy tasks₁ task tasks₂) = group-busy (map (extendt-task₂ A' B' C') tasks₁) (extendt-task₂ A' B' C' task) (map (extendt-task₂ A' B' C') tasks₂)
extendt-group₂ A' B' C' (group-idle tasks) = group-idle (map (extendt-task₂ A' B' C') tasks)

extendt-Cfg₂ : ∀{Δ n m o l idx} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → Cfg' {Δ} (_ , A ++ l ∷ B ++ C) (_ , C) idx → Cfg' {Δ} (_ , A ++ suc l ∷ B ++ C) (_ , C) idx
extendt-Cfg₂ _ _ ._ [] = []
extendt-Cfg₂ A' B' (c ∷ C') (x ∷ cfg) rewrite sym (snoc-concat {x = c} B' C') 
  = extendt-group₂ A' (B' ∷ʳ c) C' x 
    ∷ 
    extendt-Cfg₂ A' (B' ∷ʳ c) C' cfg

extendt-group' : ∀{Δ n m x} → (S : Vec ℕ (suc n) m) → (T : Vec ℕ zero n) → Task Δ (_ , S ++ x ∷ T) → Group Δ (_ , S ++ x ∷ T) x → Group Δ (_ , S ++ x ∷ T) (suc x)
extendt-group' {x = x} S T t (group-busy x₁ x₂ x₃) rewrite sym (snoc-concat {x = x} S T) = group-busy x₁ x₂ (t ∷ x₃)
extendt-group' {x = x} S T t (group-idle x₁) rewrite sym (snoc-concat {x = x} S T) = group-idle (t ∷ x₁)

extendt-Cfg : ∀{Δ n m idx} → (T : Vec ℕ zero n) → (S : Vec ℕ n m) → (gid : Fin n) → Task Δ (_ , (S ++ T)) → Cfg' {Δ} (_ , S ++ T) (_ , T) idx → Cfg' {Δ} (_ , S ++ (T [ gid ]≔ suc (lookup gid T))) (_ , T [ gid ]≔ suc (lookup gid T)) idx
extendt-Cfg [] S () _ cfg
extendt-Cfg (x ∷ T) S gid t (x₁ ∷ cfg) with down _ gid
... | just gid' rewrite append-concat {x = x} (T [ gid' ]≔ suc (lookup gid' T)) S | append-concat {x = x} T S = extendt-group T (S ∷ʳ x) gid' x₁ ∷ extendt-Cfg T (S ∷ʳ x) gid' t cfg
... | nothing = extendt-group₂ S [] T (extendt-group' S T t x₁) ∷ extendt-Cfg₂ S [] T cfg

extendt-Cfg' : ∀{Δ n m idx} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → Task Δ (_ , S ++ T) → Cfg' {Δ} (_ , S ++ T [ gid ]≔ suc (lookup gid T)) (_ , T) idx → Cfg' {Δ} (_ , S ++ T [ gid ]≔ suc (lookup gid T)) (_ , T [ gid ]≔ suc (lookup gid T)) idx
extendt-Cfg' _ [] () task []
extendt-Cfg' {n = suc n} S (t ∷ T) gid task (x ∷ cfg) with down _ gid
... | just gid' rewrite append-concat {x = t} (T [ gid' ]≔ suc (lookup gid' T)) S | append-concat {x = t} T S = x ∷ extendt-Cfg' (S ∷ʳ t) T gid' task cfg
... | nothing with x
...    | group-busy tasks₁ task' tasks₂ = group-busy tasks₁ task' (extendt-task₂ S [] T task ∷ tasks₂) ∷ cfg
...    | group-idle tasks               = group-idle (extendt-task₂ S [] T task ∷ tasks) ∷ cfg

{-
extendt-Cfg : ∀{n m l idx} → (T : Vec ℕ zero n) → (S : Vec ℕ n m) → (gid : Fin n) → Cfg' (suc _ , l ∷ (S ++ T)) (_ , T) idx → Cfg' (_ , l ∷ (S ++ (T [ gid ]≔ suc (lookup gid T)))) (_ , T) idx
extendt-Cfg ._ _ () []
extendt-Cfg (t ∷ T) S gid (x ∷ cfg) with down _ gid
extendt-Cfg (t ∷ T) S  _  (x ∷ cfg) | just gid rewrite append-concat {x = t} (T [ gid ]≔ suc (lookup gid T)) S | append-concat {x = t} T S
  = extendt-group T (_ ∷ S ∷ʳ t) gid x
    ∷
    extendt-Cfg T (S ∷ʳ t) gid cfg
extendt-Cfg (t ∷ T) S _ (x ∷ cfg) | nothing
  = extendt-group₂ (_ ∷ S) [] T x
    ∷ 
    extendt-Cfg₂ (_ ∷ S) [] T cfg
-}

extendt-CfgE' : ∀{Δ n m} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → Task Δ (_ , S ++ T) → CfgE' Δ (_ , S ++ T) (_ , T) gid → CfgE' Δ (_ , S ++ T [ gid ]≔ suc (lookup gid T)) (_ , T [ gid ]≔ suc (lookup gid T)) gid
extendt-CfgE' _ [] () _ p
extendt-CfgE' {Δ} {suc n} {m} S (x ∷ T) gid  t(head-E x₁) with down n gid
... | nothing = head-E (extendt-Cfg₂ S [] T x₁)
... | just gid' rewrite append-concat {x = x} (T [ gid' ]≔ suc (lookup gid' T)) S | sym (snoc-concat {x = x} S T) = head-E (extendt-Cfg T (S ∷ʳ x) gid' t x₁)
extendt-CfgE' S (x ∷ T) ._ t (tail-E {idx = idx} x₁ p) rewrite down-inject idx | append-concat {x = x} (T [ idx ]≔ suc (lookup idx T)) S | append-concat {x = x} T S = tail-E (extendt-group T (S ∷ʳ x) idx x₁) (extendt-CfgE' (S ∷ʳ x) T idx t p)

extendt-CfgE : ∀{Δ n}{T : Vec ℕ zero n} → (gid : Fin n) → Task Δ (_ , T) → CfgE Δ (_ , T) gid → CfgE Δ (_ , T [ gid ]≔ suc (lookup gid T)) gid
extendt-CfgE {T = T} gid t cfg = extendt-CfgE' [] T gid t cfg

extendt-CfgE₃' : ∀{Δ n m o idx t} → (A : Vec ℕ (suc n) m) → (B : Vec ℕ o n) → (C : Vec ℕ zero o) → CfgE' Δ (_ , A ++ t ∷ B ++ C) (_ , C) idx → CfgE' Δ (_ , A ++ suc t ∷ B ++ C) (_ , C) idx
extendt-CfgE₃' A' B' [] ()
extendt-CfgE₃' A' B' (c ∷ C) (head-E x) rewrite append-concat {x = c} C B' = head-E (extendt-Cfg₂ A' (B' ∷ʳ c) C x)
extendt-CfgE₃' A' B' (c ∷ C) (tail-E x cfgE) rewrite append-concat {x = c} C B' = tail-E (extendt-group₂ A' (B' ∷ʳ c) C x) (extendt-CfgE₃' A' (B' ∷ʳ c) C cfgE)

extendt-Cfg₃ : ∀{Δ n m idx} (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → Cfg' {Δ} (_ , S ++ T) (n , T) idx → Cfg' {Δ} (_ , S ++ T [ gid ]≔ suc (lookup gid T)) (n , T) idx
extendt-Cfg₃ S .[] () []
extendt-Cfg₃ {n = suc n} S (t ∷ T) gid (x ∷ cfg) with down n gid
... | just gid' rewrite append-concat {x = t} T S | append-concat {x = t} (T [ gid' ]≔ suc (lookup gid' T)) S = extendt-group T (S ∷ʳ t) gid' x ∷ extendt-Cfg₃ (S ∷ʳ t) T gid' cfg
... | nothing = extendt-group₂ S [] T x ∷ extendt-Cfg₂ S [] T cfg



extendt-CfgE₃ : ∀{Δ n m idx} → (S : Vec ℕ n m) → (T : Vec ℕ zero n) → (gid : Fin n) → CfgE' Δ (_ , S ++ T) (_ , T) idx → CfgE' Δ (_ , S ++ T [ gid ]≔ suc (lookup gid T)) (_ , T) idx
extendt-CfgE₃ S [] () _
extendt-CfgE₃ {n = suc n} S (t ∷ T) gid (head-E x) with down n gid
... | just gid' rewrite append-concat {x = t} T S | append-concat {x = t} (T [ gid' ]≔ suc (lookup gid' T)) S = head-E (extendt-Cfg₃ (S ∷ʳ t) T gid' x)
... | nothing = head-E (extendt-Cfg₂ S [] T x)
extendt-CfgE₃ {n = suc n} S (t ∷ T) gid (tail-E x cfgE) with down n gid
... | just gid' rewrite append-concat {x = t} T S | append-concat {x = t} (T [ gid' ]≔ suc (lookup gid' T)) S = tail-E (extendt-group T (S ∷ʳ t) gid' x) (extendt-CfgE₃ (S ∷ʳ t) T gid' cfgE)
... | nothing = tail-E (extendt-group₂ S [] T x) (extendt-CfgE₃' S [] T cfgE)
