module SourceProperties where

open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Data.Sum
open import Data.Product
open import Data.Vec
open import Data.Nat

open import Source


nonsense : ∀{n'}{Γ' : Ctx n'}{n}{Γ : Ctx n}{m}{Δ : FCtx m}{args : ExpList Γ Δ Γ'}{E : FunE Γ Δ Γ'}{φ}{e : Exp Γ Δ φ} →  args values → args ≡′ E [ e ] → e redex → {A : Set}{a b : A} → a == b
nonsense []-values         ()             _
nonsense (∷-values _ _ _) (exp-≡′ exp-≡) ()
nonsense (∷-values _ _ α) (val-≡′ β)     γ  = nonsense α β γ

mutual
  unique-arg-ctx : ∀{n m n' φ}{Γ : Ctx n}{Δ : FCtx m}{Γ' : Ctx n'}{E E' : FunE Γ Δ Γ'}{e e' : Exp Γ Δ φ}{args : ExpList Γ Δ Γ'} → e redex → e' redex → args ≡′ E [ e ] → args ≡′ E' [ e' ] → E == E' × e == e'
  unique-arg-ctx p₁ p₂ (exp-≡′ q₁) (exp-≡′ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl
  unique-arg-ctx () p₂ (exp-≡′ exp-≡) (val-≡′ q₂)
  unique-arg-ctx p₁ () (val-≡′ q₁) (exp-≡′ exp-≡)
  unique-arg-ctx p₁ p₂ (val-≡′ q₁) (val-≡′ q₂) with unique-arg-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx : ∀{n m τ φ}{Γ : Ctx n}{Δ : FCtx m}{E E' : E Γ Δ φ τ}{e e' : Exp Γ Δ φ}{e₀ : Exp Γ Δ τ} → e redex → e' redex → e₀ ≡ E [ e ] → e₀ ≡ E' [ e' ] → E == E' × e == e'
  unique-ctx p₁ p₂ exp-≡ exp-≡ = refl , refl
  unique-ctx =-redex () exp-≡ (=l-≡ exp-≡)
  unique-ctx =-redex () exp-≡ (=r-≡ exp-≡)
  unique-ctx ¬-redex () exp-≡ (¬-≡ exp-≡)
  unique-ctx +-redex () exp-≡ (+l-≡ exp-≡)
  unique-ctx +-redex () exp-≡ (+r-≡ exp-≡)
  unique-ctx ∨-redex () exp-≡ (∨l-≡ exp-≡)
  unique-ctx ∨-redex () exp-≡ (∨r-≡ exp-≡)
  unique-ctx ≔-redex () exp-≡ (≔-≡ exp-≡)
  unique-ctx if-redex () exp-≡ (if-≡ exp-≡)
  unique-ctx ignore-redex () exp-≡ (ignore-≡ exp-≡)
  unique-ctx send-redex () exp-≡ (sendl-≡ exp-≡)
  unique-ctx send-redex () exp-≡ (sendr-≡ exp-≡)
  unique-ctx (call-redex p₁) p₂ exp-≡ (call-≡ q₂) = nonsense p₁ q₂ p₂ , nonsense p₁ q₂ p₂
  unique-ctx (spawn-redex p₁) p₂ exp-≡ (spawn-≡ q₂) = nonsense p₁ q₂ p₂ , nonsense p₁ q₂ p₂
  unique-ctx (spawng-redex p₁) p₂ exp-≡ (spawng-≡ q₂) = nonsense p₁ q₂ p₂ , nonsense p₁ q₂ p₂
  unique-ctx ,-redex () exp-≡ (,-≡ exp-≡)

  unique-ctx p₁ =-redex (=r-≡ q₁) exp-≡ with q₁
  unique-ctx () =-redex (=r-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (=r-≡ q₁) (=l-≡ q₂) with q₂
  unique-ctx _ () (=r-≡ _) (=l-≡ _) | exp-≡
  unique-ctx p₁ p₂ (=r-≡ q₁) (=r-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ =-redex (=l-≡ q₁) exp-≡ with q₁
  unique-ctx () =-redex (=l-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (=l-≡ q₁) (=l-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl
  unique-ctx p₁ p₂ (=l-≡ q₁) (=r-≡ q₂) with q₁
  unique-ctx () _ (=l-≡ _) (=r-≡ _) | exp-≡

  unique-ctx _  ¬-redex (¬-≡ q₁) exp-≡ with q₁
  unique-ctx () ¬-redex (¬-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (¬-≡ q₁) (¬-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ +-redex (+l-≡ q₁) exp-≡ with q₁
  unique-ctx () +-redex (+l-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (+l-≡ q₁) (+l-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl
  unique-ctx p₁ p₂ (+l-≡ q₁) (+r-≡ q₂) with q₁
  unique-ctx () _ (+l-≡ _) (+r-≡ _) | exp-≡

  unique-ctx p₁ +-redex (+r-≡ q₁) exp-≡ with q₁
  unique-ctx () +-redex (+r-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (+r-≡ q₁) (+l-≡ q₂) with q₂
  unique-ctx _ () (+r-≡ _) (+l-≡ _) | exp-≡
  unique-ctx p₁ p₂ (+r-≡ q₁) (+r-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ ∨-redex (∨l-≡ q₁) exp-≡ with q₁
  unique-ctx () ∨-redex (∨l-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (∨l-≡ q₁) (∨l-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl
  unique-ctx p₁ p₂ (∨l-≡ q₁) (∨r-≡ q₂) with q₁
  unique-ctx () _ (∨l-≡ _) (∨r-≡ _) | exp-≡ 

  unique-ctx p₁ ∨-redex (∨r-≡ q₁) exp-≡ with q₁
  unique-ctx () ∨-redex (∨r-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (∨r-≡ q₁) (∨l-≡ q₂) with q₂
  unique-ctx p₁ () (∨r-≡ _) (∨l-≡ _) | exp-≡
  unique-ctx p₁ p₂ (∨r-≡ q₁) (∨r-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ ≔-redex (≔-≡ q₁) exp-≡ with q₁
  unique-ctx () ≔-redex (≔-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (≔-≡ q₁) (≔-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ if-redex (if-≡ q₁) exp-≡ with q₁
  unique-ctx () if-redex (if-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (if-≡ q₁) (if-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ ignore-redex (ignore-≡ q₁) exp-≡ with q₁
  unique-ctx () ignore-redex (ignore-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (ignore-≡ q₁) (ignore-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ send-redex (sendl-≡ q₁) exp-≡ with q₁
  unique-ctx () send-redex (sendl-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (sendl-≡ q₁) (sendl-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl
  unique-ctx p₁ p₂ (sendl-≡ q₁) (sendr-≡ q₂) with q₁
  unique-ctx () p₂ (sendl-≡ _) (sendr-≡ _) | exp-≡

  unique-ctx p₁ send-redex (sendr-≡ q₁) exp-≡ with q₁
  unique-ctx () send-redex (sendr-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (sendr-≡ q₁) (sendl-≡ q₂) with q₂
  unique-ctx _ () (sendr-≡ _) (sendl-≡ _) | exp-≡
  unique-ctx p₁ p₂ (sendr-≡ q₁) (sendr-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ (call-redex p₂) (call-≡ q₁) exp-≡ = nonsense p₂ q₁ p₁ , nonsense p₂ q₁ p₁
  unique-ctx p₁ p₂ (call-≡ q₁) (call-≡ q₂) with unique-arg-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ (spawn-redex p₂) (spawn-≡ q₁) exp-≡ = nonsense p₂ q₁ p₁ , nonsense p₂ q₁ p₁
  unique-ctx p₁ p₂ (spawn-≡ q₁) (spawn-≡ q₂) with unique-arg-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ (spawng-redex p₂) (spawng-≡ q₁) exp-≡ = nonsense p₂ q₁ p₁ , nonsense p₂ q₁ p₁
  unique-ctx p₁ p₂ (spawng-≡ q₁) (spawng-≡ q₂) with unique-arg-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

  unique-ctx p₁ ,-redex (,-≡ q₁) exp-≡ with q₁
  unique-ctx () ,-redex (,-≡ _) exp-≡ | exp-≡
  unique-ctx p₁ p₂ (,-≡ q₁) (,-≡ q₂) with unique-ctx p₁ p₂ q₁ q₂
  ... | refl , refl = refl , refl

mutual
  unique-arg-ctx-hole : ∀{n}{Γ : Ctx n}{m}{Δ : FCtx m}{n'}{Γ' : Ctx n'}{φ φ'}{E : FunE Γ Δ Γ'}{E' : FunE Γ Δ Γ'}{e : Exp Γ Δ φ}{e' : Exp Γ Δ φ'}{args : ExpList Γ Δ Γ'} → e redex → e' redex → args ≡′ E [ e ] → args ≡′ E' [ e' ] → φ == φ'
  unique-arg-ctx-hole p₁ p₂ (exp-≡′ q₁)    (exp-≡′ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂
  unique-arg-ctx-hole () _  (exp-≡′ exp-≡) (val-≡′ _)
  unique-arg-ctx-hole _  () (val-≡′ _)     (exp-≡′ exp-≡)
  unique-arg-ctx-hole p₁ p₂ (val-≡′ q₁)    (val-≡′ q₂) = unique-arg-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole : ∀{n}{Γ : Ctx n}{m}{Δ : FCtx m}{τ φ φ'}{E' : E Γ Δ φ' τ}{E : E Γ Δ φ τ}{e e'}{e₀ : Exp Γ Δ τ} → e redex → e' redex → e₀ ≡ E [ e ] → e₀ ≡ E' [ e' ] → φ == φ'
  unique-ctx-hole p₁      p₂ exp-≡ exp-≡     = refl
  unique-ctx-hole =-redex () exp-≡ (=l-≡ exp-≡)
  unique-ctx-hole =-redex () exp-≡ (=r-≡ exp-≡)
  unique-ctx-hole ¬-redex () exp-≡ (¬-≡ exp-≡)
  unique-ctx-hole +-redex () exp-≡ (+l-≡ exp-≡)
  unique-ctx-hole +-redex () exp-≡ (+r-≡ exp-≡)
  unique-ctx-hole ∨-redex () exp-≡ (∨l-≡ exp-≡)
  unique-ctx-hole ∨-redex () exp-≡ (∨r-≡ exp-≡)
  unique-ctx-hole ≔-redex () exp-≡ (≔-≡ exp-≡)
  unique-ctx-hole if-redex () exp-≡ (if-≡ exp-≡)
  unique-ctx-hole ignore-redex () exp-≡ (ignore-≡ exp-≡)
  unique-ctx-hole send-redex () exp-≡ (sendl-≡ exp-≡)
  unique-ctx-hole send-redex () exp-≡ (sendr-≡ exp-≡)
  unique-ctx-hole (call-redex p₁) p₂ exp-≡ (call-≡ q₂) = nonsense p₁ q₂ p₂
  unique-ctx-hole (spawn-redex p₁) p₂ exp-≡ (spawn-≡ q₂) = nonsense p₁ q₂ p₂
  unique-ctx-hole (spawng-redex p₁) p₂ exp-≡ (spawng-≡ q₂) = nonsense p₁ q₂ p₂
  unique-ctx-hole ,-redex () exp-≡ (,-≡ exp-≡)

  unique-ctx-hole p₁ =-redex (=r-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () =-redex (=r-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (=r-≡ q₁) (=l-≡ q₂) with q₂
  unique-ctx-hole _ () (=r-≡ _) (=l-≡ _) | exp-≡
  unique-ctx-hole p₁ p₂ (=r-≡ q₁) (=r-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ =-redex (=l-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () =-redex (=l-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (=l-≡ q₁) (=l-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂
  unique-ctx-hole p₁ p₂ (=l-≡ q₁) (=r-≡ q₂) with q₁
  unique-ctx-hole () _ (=l-≡ _) (=r-≡ _) | exp-≡

  unique-ctx-hole p₁ ¬-redex (¬-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () ¬-redex (¬-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (¬-≡ q₁) (¬-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ +-redex (+l-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () +-redex (+l-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (+l-≡ q₁) (+l-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂
  unique-ctx-hole p₁ p₂ (+l-≡ q₁) (+r-≡ q₂) with q₁
  unique-ctx-hole () _ (+l-≡ _) (+r-≡ _) | exp-≡

  unique-ctx-hole p₁ +-redex (+r-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () +-redex (+r-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (+r-≡ q₁) (+l-≡ q₂) with q₂
  unique-ctx-hole _ () (+r-≡ _) (+l-≡ _) | exp-≡
  unique-ctx-hole p₁ p₂ (+r-≡ q₁) (+r-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ ∨-redex (∨l-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () ∨-redex (∨l-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (∨l-≡ q₁) (∨l-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂
  unique-ctx-hole p₁ p₂ (∨l-≡ q₁) (∨r-≡ q₂) with q₁
  unique-ctx-hole () _ (∨l-≡ _) (∨r-≡ _) | exp-≡ 

  unique-ctx-hole p₁ ∨-redex (∨r-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () ∨-redex (∨r-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (∨r-≡ q₁) (∨l-≡ q₂) with q₂
  unique-ctx-hole p₁ () (∨r-≡ _) (∨l-≡ _) | exp-≡
  unique-ctx-hole p₁ p₂ (∨r-≡ q₁) (∨r-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ ≔-redex (≔-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () ≔-redex (≔-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (≔-≡ q₁) (≔-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ if-redex (if-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () if-redex (if-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (if-≡ q₁) (if-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ ignore-redex (ignore-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () ignore-redex (ignore-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (ignore-≡ q₁) (ignore-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ send-redex (sendl-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () send-redex (sendl-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (sendl-≡ q₁) (sendl-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂
  unique-ctx-hole p₁ p₂ (sendl-≡ q₁) (sendr-≡ q₂) with q₁
  unique-ctx-hole () p₂ (sendl-≡ _) (sendr-≡ _) | exp-≡

  unique-ctx-hole p₁ send-redex (sendr-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () send-redex (sendr-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (sendr-≡ q₁) (sendl-≡ q₂) with q₂
  unique-ctx-hole _ () (sendr-≡ _) (sendl-≡ _) | exp-≡
  unique-ctx-hole p₁ p₂ (sendr-≡ q₁) (sendr-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ (call-redex p₂) (call-≡ q₁) exp-≡ = nonsense p₂ q₁ p₁
  unique-ctx-hole p₁ p₂ (call-≡ q₁) (call-≡ q₂) = unique-arg-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ (spawn-redex p₂) (spawn-≡ q₁) exp-≡ = nonsense p₂ q₁ p₁
  unique-ctx-hole p₁ p₂ (spawn-≡ q₁) (spawn-≡ q₂) = unique-arg-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ (spawng-redex p₂) (spawng-≡ q₁) exp-≡ = nonsense p₂ q₁ p₁
  unique-ctx-hole p₁ p₂ (spawng-≡ q₁) (spawng-≡ q₂) = unique-arg-ctx-hole p₁ p₂ q₁ q₂

  unique-ctx-hole p₁ ,-redex (,-≡ q₁) exp-≡ with q₁
  unique-ctx-hole () ,-redex (,-≡ _) exp-≡ | exp-≡
  unique-ctx-hole p₁ p₂ (,-≡ q₁) (,-≡ q₂) = unique-ctx-hole p₁ p₂ q₁ q₂

mutual
  arg-split : ∀{n}{Γ : Ctx n}{m}{Δ : FCtx m}{n'}{Γ' : Ctx n'} → (args : ExpList Γ Δ Γ') → (args values) ⊎ ∃ λ φ → ∃₂ λ FunE (e' : Exp Γ Δ φ) → args ≡′ FunE [ e' ] × e' redex
  arg-split [] = inj₁ []-values
  arg-split (x  ∷ args) with split x
  arg-split (._ ∷ args) | inj₁ (x , refl) with arg-split args
  arg-split (._ ∷ args) | inj₁ (x , refl) | inj₁ p = inj₁ (∷-values x args p)
  arg-split (._ ∷ args) | inj₁ (x , refl) | inj₂ (α , β , γ , δ , ε) = inj₂ (α , val x β , γ , val-≡′ δ , ε)
  arg-split (x  ∷ args) | inj₂ (α , β , γ , δ , ε) = inj₂ (α , exp β args , γ , exp-≡′ δ , ε)


  split : ∀{n}{Γ : Ctx n}{m}{Δ : FCtx m}{τ} → (e : Exp Γ Δ τ) → (∃ λ v → e == (val v)) ⊎ ∃ λ φ → ∃₂ λ E (e' : Exp Γ Δ φ) → e ≡ E [ e' ] × e' redex
  split (var x) = inj₂ (_ , □ , var x , exp-≡ , var-redex)

  split (val y) = inj₁ (y , refl)

  split (e₀ ≐ _ ) with   split e₀
  split (._ ≐ e₁) | inj₁ (x , refl) with   split e₁
  split (._ ≐ ._) | inj₁ (x , refl)          | inj₁ (y , refl)          = inj₂ (_ , □       , ((val x) ≐ (val y)) , exp-≡ , =-redex)
  split (._ ≐ e₁) | inj₁ (x , refl)          | inj₂ (α , β , γ , δ , ε) = inj₂ (α , =r-E x β  , γ                   , =r-≡ δ , ε)
  split (_  ≐ e₁) | inj₂ (α , β , γ , δ , ε)                            = inj₂ (α , =l-E β e₁ , γ                   , =l-≡ δ , ε)

  split (¬ ex) with   split ex
  split (¬ ._) | inj₁ (_ , refl)          = inj₂ (Bo , □ , _ , exp-≡ , ¬-redex)
  split (¬ _)  | inj₂ (α , β , γ , δ , ε) = inj₂ (α , ¬-E β , γ , ¬-≡ δ , ε)

  split (e₀ ∔ e₁) with   split e₀
  split (e₀ ∔ e₁) | inj₁ x with   split e₁
  split (._ ∔ ._) | inj₁ (x , refl)          | inj₁ (y , refl)          = inj₂ (_ , □ , (val x) ∔ (val y) , exp-≡ , +-redex)
  split (._ ∔ e₁) | inj₁ (x , refl)          | inj₂ (α , β , γ , δ , ε) = inj₂ (α , +r-E x β , γ , +r-≡ δ , ε)
  split (e₀ ∔ e₁) | inj₂ (α , β , γ , δ , ε)                            = inj₂ (α , +l-E β e₁ , γ , +l-≡ δ , ε)

  split (e₀ ⊻ e₁) with   split e₀
  split (e₀ ⊻ e₁) | inj₁ x with   split e₁
  split (._ ⊻ ._) | inj₁ (x , refl)          | inj₁ (y , refl)          = inj₂ (_ , □ , (val x) ⊻ (val y) , exp-≡ , ∨-redex)
  split (._ ⊻ e₁) | inj₁ (x , refl)          | inj₂ (α , β , γ , δ , ε) = inj₂ (α , ∨r-E x β , γ , ∨r-≡ δ , ε)
  split (e₀ ⊻ e₁) | inj₂ (α , β , γ , δ , ε)                            = inj₂ (α , ∨l-E β e₁ , γ , ∨l-≡ δ , ε)

  split avail = inj₂ (_ , □ , _ , exp-≡ , avail-redex)

  split (fun （ args ）) with arg-split args
  split (fun （ args ）) | inj₁ p = inj₂ (_ , □ , _ , exp-≡ , call-redex p)
  split (fun （ args ）) | inj₂ (α , β , γ , δ , ε) = inj₂ (α , call-E fun β , γ , call-≡ δ , ε)

  split (spawn fun args) with arg-split args
  ... | inj₁ p                   = inj₂ (_ , □ , _ , exp-≡ , spawn-redex p)
  ... | inj₂ (α , β , γ , δ , ε) = inj₂ (α , spawn-E fun β , γ , spawn-≡ δ , ε)

  split (spawng fun args) with arg-split args
  ... | inj₁ p                   = inj₂ (_ , □ , _ , exp-≡ , spawng-redex p)
  ... | inj₂ (α , β , γ , δ , ε) = inj₂ (α , spawng-E fun β , γ , spawng-≡ δ , ε)

  split yield = inj₂ (_ , □ , _ , exp-≡ , yield-redex)
    
  split (x ≔ ex) with   split ex
  split (x ≔ ._) | inj₁ (y , refl) = inj₂ (_ , □ , _ , exp-≡ , ≔-redex)
  split (x ≔ ex) | inj₂ (α , β , γ , δ , ε) = inj₂ (α , ≔-E x β , γ , ≔-≡ δ , ε)

  split skip = inj₂ (_ , □ , _ , exp-≡ , skip-redex)

  split (e₀ , e₁) with split e₀
  split (._ , e₁) | inj₁ (U , refl) = inj₂ (_ , □ , _ , exp-≡ , ,-redex)
  split (e₀ , e₁) | inj₂ (α , β , γ , δ , ε) = inj₂ (α , ,-E β e₁ , γ , ,-≡ δ , ε)

  split (If ex then _ else _) with   split ex
  split (If ._ then _ else _)   | inj₁ (_ , refl)          = inj₂ (_ , □ , _ , exp-≡ , if-redex)
  split (If ex then e₁ else e₂) | inj₂ (α , β , γ , δ , ε) = inj₂ (α , if-E β e₁ e₂ , γ , if-≡ δ , ε)

  split (While _ do _) = inj₂ (_ , □ , _ , exp-≡ , while-redex)

  split (send e₁ _) with   split e₁
  split (send ._ e₂) | inj₁ (_ , refl) with   split e₂
  split (send ._ ._) | inj₁ (_ , refl)          | inj₁ (_ , refl)          = inj₂ (_ , □ , _ , exp-≡ , send-redex)
  split (send ._ e₂) | inj₁ (x , refl)          | inj₂ (α , β , γ , δ , ε) = inj₂ (α , sendr-E x β , γ , sendr-≡ δ , ε)
  split (send e₁ e₂) | inj₂ (α , β , γ , δ , ε)                            = inj₂ (α , sendl-E β e₂ , γ , sendl-≡ δ , ε)

  split (receive _ _ _ _) = inj₂ (_ , □ , _ , exp-≡ , receive-redex)

  split (ignore ex) with   split ex
  split (ignore ._) | inj₁ (_ , refl)          = inj₂ (_ , □ , _ , exp-≡ , ignore-redex)
  split (ignore _)  | inj₂ (α , β , γ , δ , ε) = inj₂ (α , ignore-E β , γ , ignore-≡ δ , ε)
