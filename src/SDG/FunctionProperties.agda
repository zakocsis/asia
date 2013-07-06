open import SDG.Base

module SDG.FunctionProperties
  (ℝ : Set)
  (sf : SmoothField ℝ)
where

open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst₂; _≡_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Function using (id; const)

import SDG.Derivative.Definition
import SDG.Derivative.Properties
import SDG.Integral.Definition
open module Dummy1 = SDG.Derivative.Definition ℝ sf
open module Dummy2 = SDG.Derivative.Properties ℝ sf
open module Dummy3 = SDG.Integral.Definition   ℝ sf

open Eq.≡-Reasoning
open SmoothField sf


-- dx/dx = 1
∂-id : ∀ (x : ℝ) → ∂ id x ≡ const 1# x
∂-id = ∂-computation id (const 1#) computation where
  computation : ∀ (x ε : ℝ) → nils ε → x + ε ≡ x + ε * 1#
  computation x ε Δε = cong (λ p → x + p) (sym (proj₂ *-identity ε))

-- dc/dx = 0
∂-const : ∀ (c x : ℝ) → ∂ (const c) x ≡ const 0# x
∂-const c = ∂-computation (const c) (const 0#) computation where
  computation : ∀ (x ε : ℝ) → nils ε → c ≡ c + ε * 0#
  computation x ε Δε = begin
      c
    ≡⟨ sym (proj₂ +-identity c) ⟩
      c + 0#
    ≡⟨ cong (λ p → c + p) (sym (proj₂ zero ε)) ⟩
      c + ε * 0#
    ∎

∫-const : ∀ (c : ℝ) → Integrable (const c)
∫-const c = fundamental-thm-2 (const c) (_*_ c) goal where
  computation : ∀ (x ε : ℝ) → nils ε →
                c * (x + ε) ≡ c * x + ε * c
  computation x ε Δε =
    begin
      c * (x + ε)
    ≡⟨ proj₁ distrib c x ε ⟩
      c * x + c * ε
    ≡⟨ cong₂ _+_ refl (*-comm c ε) ⟩
      c * x + ε * c
    ∎
  goal : ∀ (x : ℝ) → ∂ (_*_ c) x ≡ c
  goal = ∂-computation (_*_ c) (const c) computation

-- Notes: without the Fundamental Theorem of Calculus,
--        proving that constant functions are integrable
--        would take 53 lines.

-- Notes: there is no proof that id is integrable.
--        That is not too surprising, as the identity
--        function is not integrable in every SF.
--        There are SFs of characteristic 2, i.e.
--        where 2 = 0, and there, id has no primitive,
--        and so is not integrable.