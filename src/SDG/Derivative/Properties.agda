open import SDG.Base

module SDG.Derivative.Properties
  (ℝ : Set)
  (sf : SmoothField ℝ)
where

import SDG.Derivative.Definition
open module Dummy = SDG.Derivative.Definition ℝ sf

open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst₂; _≡_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)


open Eq.≡-Reasoning
open SmoothField sf

_⊗_ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
(f ⊗ g) x = f x * g x
_∘_ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
(f ∘ g) x = f (g x)

-- the chain rule for derivatives
∂-∘-rule : ∀ (f g : ℝ → ℝ) → ∀ (x : ℝ) → ∂ (f ∘ g) x ≡ (∂ g x) * ∂ f (g x)
∂-∘-rule f g = ∂-computation (f ∘ g) (∂ g ⊗ (∂ f ∘ g)) computation where
  computation : ∀ (x ε : ℝ) → nils ε →
                (f ∘ g) (x + ε) ≡ (f ∘ g) x + ε * (∂ g ⊗ (∂ f ∘ g)) x
  computation x ε Δε = begin
      (f ∘ g) (x + ε)
    ≡⟨ cong f (kock-lawvere g x ε Δε) ⟩
      f (g x + ε * ∂ g x)
    ≡⟨ kock-lawvere f (g x) (ε * ∂ g x) (*-nils (∂ g x) (∂ g x) ε Δε) ⟩
      f (g x) + (ε * ∂ g x) * ∂ f (g x)
    ≡⟨ +-cong refl (*-assoc ε (∂ g x) (∂ f (g x))) ⟩
      f (g x) + ε * (∂ g x * ∂ f (g x))
    ∎

-- I'll prove the sum and product rules when the Smooth Ring Solver is ready