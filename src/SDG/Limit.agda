open import SDG.Base

module SDG.Limit
  (ℝ : Set)
  (sf : SmoothField ℝ)
where

open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst₂; _≡_)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ)

import SDG.Derivative.Definition
open module Dummy = SDG.Derivative.Definition ℝ sf

open Eq.≡-Reasoning
open SmoothField sf

-- This definition of limit is very subtle,
-- and it took me many tries to get it right.
record Limit_≡ (a : ℝ → ℝ → ℝ) (b : ℝ → ℝ) : Set where
  field
    Limit-val : ℝ
    Limit-ind : ∀ (s : ℝ) → (∀ (ε : ℝ) → nils ε → a s ε ≡ b ε) → s ≡ Limit-val
    Limit-bas : a Limit-val 0# ≡ b 0#
    Limit-der : ∂ (a Limit-val) 0# ≡ ∂ b 0#

  Limit-sol : ∀ (ε : ℝ) → nils ε → a Limit-val ε ≡ b ε
  Limit-sol ε Δε = 
    begin
      a Limit-val ε
    ≡⟨ cong (a Limit-val) (sym (proj₁ +-identity ε)) ⟩
      a Limit-val (0# + ε)
    ≡⟨ kock-lawvere (a Limit-val) 0# ε Δε ⟩
      a Limit-val 0# + ε * ∂ (a Limit-val) 0#
    ≡⟨ cong₂ _+_ Limit-bas refl ⟩
      b 0# + ε * ∂ (a Limit-val) 0#
    ≡⟨ cong (λ p → b 0# + ε * p) Limit-der ⟩
      b 0# + ε * ∂ b 0#
    ≡⟨ sym (kock-lawvere b 0# ε Δε) ⟩
      b (0# + ε)
    ≡⟨ cong b (proj₁ +-identity ε) ⟩
      b ε
    ∎
     
open Limit_≡ public

uniqueness : ∀ (a : ℝ → ℝ → ℝ) → ∀ (b : ℝ → ℝ) →
             ∀ (p q : Limit a ≡ b) → Limit-val p ≡ Limit-val q
uniqueness a b p q = Q.Limit-ind P.Limit-val P.Limit-sol where
  open module P = Limit_≡ p
  open module Q = Limit_≡ q