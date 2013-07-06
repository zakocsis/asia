open import SDG.Base

module SDG.Derivative.Definition
  (ℝ : Set)
  (sf : SmoothField ℝ)
where

open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst₂; _≡_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)


open Eq.≡-Reasoning
open SmoothField sf

-- the definition of the derivative
∂ : (ℝ → ℝ) → ℝ → ℝ
(∂ f) x = der# (λ y → f (x + y))

-- two important theorems

-- the Kock-Lawvere theorem:
kock-lawvere : ∀ (f : ℝ → ℝ) → ∀ (x ε : ℝ) → nils ε →
               f (x + ε) ≡ f x + ε * (∂ f) x
kock-lawvere f x ε Δε =
  begin
    f (x + ε)
  ≡⟨ refl ⟩
    g ε
  ≡⟨ der#-microlinear g ε Δε ⟩
    f (x + 0#) + ε * ∂ f x
  ≡⟨ cong (λ P → f P + ε * ∂ f x) (proj₂ +-identity x) ⟩
    f x + ε * (∂ f) x
  ∎ where
  g : ℝ → ℝ
  g y = f (x + y)

-- Derivatives by computation: an important proof tactic,
-- and an analogue of the uniqueness clause of the smoothness axiom

∂-computation : ∀ (f f' : ℝ → ℝ) →
               (∀ (x ε : ℝ) → nils ε → f (x + ε) ≡ f x + ε * f' x) →
               ∀ (x : ℝ) → ∂ f x ≡ f' x
∂-computation f f' premise x = sym (microcancellation (f' x) (∂ f x) step2) where
  step1 : ∀ (ε : ℝ) → nils ε → f x + ε * f' x ≡ f x + ε * ∂ f x
  step1 ε Δε =
    begin
      f x + ε * f' x
    ≡⟨ sym (premise x ε Δε) ⟩
      f (x + ε)
    ≡⟨ kock-lawvere f x ε Δε ⟩
      f x + ε * ∂ f x
    ∎
  step2 : ∀ (ε : ℝ) → nils ε → ε * f' x ≡ ε * ∂ f x
  step2 ε Δε = 
    begin
      ε * f' x
    ≡⟨ sym (+-absorb (f x) (ε * f' x)) ⟩
      ~ f x + (f x + ε * f' x)
    ≡⟨ +-cong refl (step1 ε Δε) ⟩
      ~ f x + (f x + ε * ∂ f x)
    ≡⟨ +-absorb (f x) (ε * ∂ f x) ⟩
      ε * ∂ f x
    ∎