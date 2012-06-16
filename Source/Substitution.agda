module Source.Substitution where

open import Data.List

open import Source.Syntax

Ren : CCtx → CCtx → Set
Ren Φ Ψ = ∀{τ} → Const Φ τ → Const Ψ τ

wk : ∀{Φ Ψ τ} → Ren Φ Ψ → Ren (τ ∷ Φ) (τ ∷ Ψ)
wk f (z ._) = z _
wk f (s v) = s (f v)

ren : ∀{Δ Γ Φ Ψ T τ} → Ren Φ Ψ → Exp Δ Γ Φ T τ → Exp Δ Γ Ψ T τ

ren-args : ∀{Δ Γ Φ Ψ T Λ} → Ren Φ Ψ → ExpList Δ Γ Φ T Λ  → ExpList Δ Γ Ψ T Λ
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

Sub : FCtx → Ctx → TCtx → CCtx → CCtx → Set
Sub Δ Γ T Φ Ψ = ∀{τ} → Const Φ τ → Exp Δ Γ Ψ T τ

lift-sub : ∀{Δ Γ T Φ Ψ σ} → Sub Δ Γ T Φ Ψ → Sub Δ Γ T (σ ∷ Φ) (σ ∷ Ψ)
lift-sub f (z ._) = const (z _)
lift-sub f (s c) = ren s (f c)

sub : ∀{Δ Γ T Φ Ψ τ} → Sub Δ Γ T Φ Ψ → Exp Δ Γ Φ T τ → Exp Δ Γ Ψ T τ

sub-args : ∀{Δ Γ T Φ Ψ Λ} → Sub Δ Γ T Φ Ψ → ExpList Δ Γ Φ T Λ → ExpList Δ Γ Ψ T Λ
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

_::_ : ∀{Δ Γ T Φ Ψ τ} → Exp Δ Γ Ψ T τ → Sub Δ Γ T Φ Ψ → Sub Δ Γ T (τ ∷ Φ) Ψ
(t :: f) (z ._) = t
(t :: f) (s e) = f e

subst-const : ∀{Δ Γ Ξ T ξ τ} → Val T ξ → Exp Δ Γ (ξ ∷ Ξ) T τ → Exp Δ Γ Ξ T τ
subst-const v e = sub (val v :: const) e
