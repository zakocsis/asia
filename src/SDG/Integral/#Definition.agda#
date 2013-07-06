open import SDG.Base

module SDG.Integral.Definition
  (ℝ : Set)
  (sf : SmoothField ℝ)
where

import SDG.Derivative.Definition
open module Dummy = SDG.Derivative.Definition ℝ sf

open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst₂; _≡_)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ)


open Eq.≡-Reasoning
open SmoothField sf

Primitive : (ℝ → ℝ) → (ℝ → ℝ) → Set
Primitive f F = ∀ (x : ℝ) → ∂ F x ≡ f x


-- A function is Integrable iff it has an area measure
-- satisfying the following axioms:
-- (finite) additivity: the whole is the sum of its parts
-- smoothness: the area of an infinitesimal rectangle is (base * height).
record Integrable (f : ℝ → ℝ) : Set where
  field
    ∫ : ℝ → ℝ → ℝ
    ∫-additive  : ∀ (x y z : ℝ) →
                  ∫ x z ≡ ∫ x y + ∫ y z
    ∫-smooth    : ∀ (x ε : ℝ) → nils ε →
                  ∫ x (x + ε) ≡ ε * f x

  -- ∫ x x = 0, as zero is an infinitesimal
  ∫-zero : ∀ (x : ℝ) → ∫ x x ≡ 0#
  ∫-zero x = 
    begin
      ∫ x x
    ≡⟨ cong (∫ x) (sym (proj₂ +-identity x)) ⟩
      ∫ x (x + 0#)
    ≡⟨ ∫-smooth x 0# (proj₁ zero 0#) ⟩
      0# * f x
    ≡⟨ proj₁ zero (f x) ⟩
      0#
    ∎

  -- The Fundamental Theorem of Calculus
  -- Part 1: Derivative is the left inverse of definite integral
  fundamental-thm-1 : ∀ (a x : ℝ) → ∂ (∫ a) x ≡ f x
  fundamental-thm-1 a = ∂-computation (∫ a) f computation where
    computation : ∀ (b ε : ℝ) → nils ε → ∫ a (b + ε) ≡ ∫ a b + (ε * f b)
    computation b ε Δε =
      begin
        ∫ a (b + ε)
      ≡⟨ ∫-additive a b (b + ε) ⟩
        ∫ a b + ∫ b (b + ε)
      ≡⟨ cong (λ p → ∫ a b + p) (∫-smooth b ε Δε) ⟩
        ∫ a b + ε * f b
      ∎

  -- A simple corollary of the Fundamental Theorem is that
  -- every integrable function has primitive functions
  ∫-primitive : Primitive f (∫ 0#)
  ∫-primitive = fundamental-thm-1 0#


-- The Fundamental Theorem of Calculus
-- Part 2: A primitive function of f gives rise to an area measure
fundamental-thm-2 : ∀ (f F : ℝ → ℝ) → Primitive f F → Integrable f
fundamental-thm-2 f F premise = record { ∫          = ∫
                                       ; ∫-additive = ∫-additive
                                       ; ∫-smooth   = ∫-smooth
                                       } where
  ∫ : ℝ → ℝ → ℝ
  ∫ x y = F y - F x
  ∫-additive : ∀ (x y z : ℝ) → ∫ x z ≡ ∫ x y + ∫ y z
  ∫-additive x y z =
    begin
      ∫ x z
    ≡⟨ sym (proj₂ +-identity (F z - F x)) ⟩
      F z - F x + 0#
    ≡⟨ cong₂ _+_ refl (sym (proj₁ +-inverse (F y))) ⟩
      F z - F x + (~ F y + F y)
    ≡⟨ sym (+-assoc (F z - F x) (~ F y) (F y)) ⟩
      (F z - F x - F y) + F y
    ≡⟨ cong₂ _+_ (+-assoc (F z) (~ F x) (~ F y)) refl ⟩
      (F z + (~ F x - F y)) + F y
    ≡⟨ cong (λ p → (F z + p) + F y) (+-comm (~ F x) (~ F y)) ⟩
      (F z + (~ F y - F x)) + F y
    ≡⟨ cong₂ _+_ (sym (+-assoc (F z) (~ F y) (~ F x))) refl ⟩
      (F z - F y - F x) + F y
    ≡⟨ +-assoc (F z - F y) (~ F x) (F y) ⟩
      F z - F y + (~ F x + F y)
    ≡⟨ cong₂ _+_ refl (+-comm (~ F x) (F y)) ⟩
      (F z - F y) + (F y - F x)
    ≡⟨ +-comm (∫ y z) (∫ x y) ⟩
      ∫ x y + ∫ y z
    ∎
  ∫-smooth : (x ε : ℝ) → nils ε → ∫ x (x + ε) ≡ ε * f x
  ∫-smooth x ε Δε =
    begin
      ∫ x (x + ε)
    ≡⟨ refl ⟩
      F (x + ε) - F x
    ≡⟨ cong₂ _+_ (kock-lawvere F x ε Δε) refl ⟩
      (F x + ε * ∂ F x) - F x
    ≡⟨ cong₂ _+_ (+-comm (F x) (ε * ∂ F x)) refl ⟩
      (ε * ∂ F x + F x) - F x
    ≡⟨ +-assoc (ε * ∂ F x) (F x) (~ F x) ⟩
      ε * ∂ F x + (F x - F x)
    ≡⟨ cong₂ _+_ refl (proj₂ +-inverse (F x)) ⟩
      ε * ∂ F x + 0#
    ≡⟨ proj₂ +-identity (ε * ∂ F x) ⟩
      ε * ∂ F x
    ≡⟨ cong₂ _*_ refl (premise x) ⟩
      ε * f x
    ∎

-- Notes on the above Fundamental Theorems:
-- Classically, "functions having a primitive" and "integrable functions"
-- coincide only in the continuous case.
-- In particular, classically there is an integrable function that has
-- no primitive on any interval, and there is a function that has a primitive
-- but is not Riemann-integrable.
-- Even the Lebesgue theory can only rule out the latter case.

-- Notes: I have made no attempt to show that area measures are unique.
--        This is true when the SF is a real number object (has ℚ as subring),
--        but the only proof I know requires the general case of Taylor's
--        theorem. In other SFs, the result may even fail.

-- Notes: We may do uniqueness after all: if we prove that every primitive
--        function of f gives rise to the same area measure, then
--        we can prove uniqueness.