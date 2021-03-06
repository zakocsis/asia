module SDG.Base where

open import Algebra
open import Algebra.Structures
import Level as L
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; cong₂; subst₂; _≡_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open Eq.≡-Reasoning
open import Algebra.RingSolver.AlmostCommutativeRing

record SmoothField (ℝ : Set) : Set where
  infixl 7 _*_
  infixl 6 _+_
  field
    -- ℝ satisfies the signature for weak fields
    _+_ : ℝ → ℝ → ℝ
    _*_ : ℝ → ℝ → ℝ
    ~_ : ℝ → ℝ
    0# : ℝ
    1# : ℝ
    inv : (x : ℝ) → (x ≡ 0# → ⊥) → ℝ

    -- ℝ is a commutative ring with identity
    ℝ-ring : IsCommutativeRing _≡_ _+_ _*_ ~_ 0# 1#
    -- ℝ is a weak field
    *-inverse : ∀ {x} → (p : x ≡ 0# → ⊥) → x * inv x p ≡ 1#

    -- ℝ is smooth
    der# : (ℝ → ℝ) → ℝ
    der#-microlinear : ∀ (f : ℝ → ℝ) → ∀ (ε : ℝ) → ε * ε ≡ 0# →
                       f ε ≡ (f 0#) + ε * (der# f)
    der#-unique : ∀ (f : ℝ → ℝ) → ∀ (der₁ der₂ : ℝ) →
                  (∀ (ε : ℝ) → ε * ε ≡ 0# → f ε ≡ (f 0#) + ε * der₁) →
                  (∀ (ε : ℝ) → ε * ε ≡ 0# → f ε ≡ (f 0#) + ε * der₂) →
                  der₁ ≡ der₂

  open IsCommutativeRing ℝ-ring public renaming (-‿inverse to +-inverse; -‿cong to ~-cong)

  import Data.Nat
  module Nat = Data.Nat

  -- Nilsquare infinitesimal
  nils : ℝ → Set
  nils ε = ε * ε ≡ 0#

  module CoeffsWith (ε : ℝ) (Δε : nils ε) where
    
    _⊕_ = Nat._+_
    _⊛_ = Nat._*_

    data Coeffs : Set where
      ε*+ : Nat.ℕ → Coeffs
      ε*- : Nat.ℕ → Coeffs
    
    cadd : Coeffs → Coeffs → Coeffs
    cadd (ε*+ a) (ε*+ b) = ε*+ (a ⊕ b)
    cadd (ε*+ 0) (ε*- b) = ε*- b
    cadd (ε*+ (Nat.suc a)) (ε*- 0) = ε*+ (Nat.suc a)
    cadd (ε*+ (Nat.suc a)) (ε*- (Nat.suc b)) = cadd (ε*+ a) (ε*- b)
    cadd (ε*- 0) (ε*+ b) = ε*+ b
    cadd (ε*- (Nat.suc a)) (ε*+ Nat.zero) = ε*- (Nat.suc a)
    cadd (ε*- (Nat.suc a)) (ε*+ (Nat.suc b)) = cadd (ε*- a) (ε*+ b)
    cadd (ε*- a) (ε*- b) = ε*- (a ⊕ b)

    cmul : Coeffs → Coeffs → Coeffs
    cmul a b = ε*+ 0

    cneg : Coeffs → Coeffs
    cneg (ε*+ a) = ε*- a
    cneg (ε*- a) = ε*+ a

    postulate ε*0 : ε*- 0 ≡ ε*+ 0

    cast : Coeffs → ℝ
    cast (ε*+ 0) = 0#
    cast (ε*- 0) = 0#
    cast (ε*+ 1) = ε
    cast (ε*- 1) = ~ ε
    cast (ε*+ (Nat.suc a)) = ε + cast (ε*+ a)
    cast (ε*- (Nat.suc a)) = ~ ε + cast (ε*- a)
    {-
    cast (x + ε* y) = primcast x + ε * primcast y                            -- x : ℤ, y : ℤ
    primcast (+ zero) = 0#
    primcast (+ suc zero) =   1#
    primcast (- suc zero) = ~ 1#

    -}
    
    
    CoeffRing : RawRing L.zero
    CoeffRing = record { Carrier = Coeffs
                       ; _+_ = cadd
                       ; _*_ = cmul
                       ; -_ = cneg
                       ; 0# = ε*+ 0
                       ; 1# = ε*+ 1
                       }
    
    CR-ℝ : CommutativeRing L.zero L.zero
    CR-ℝ = record { Carrier = ℝ
                  ; _≈_ = _≡_
                  ; _+_ = _+_
                  ; _*_ = _*_
                  ; -_ = ~_
                  ; 0# = 0#
                  ; 1# = 1#
                  ; isCommutativeRing = ℝ-ring
                  }
    
    ACR-ℝ : AlmostCommutativeRing L.zero L.zero
    ACR-ℝ = fromCommutativeRing CR-ℝ
    
    casts : CoeffRing -Raw-AlmostCommutative⟶ ACR-ℝ
    casts = record { ⟦_⟧    = cast
                   ; +-homo = {!!}
                   ; *-homo = admitted
                   ; -‿homo = admitted
                   ; 0-homo = admitted
                   ; 1-homo = admitted
                   } where
      postulate admitted : ∀ {A : Set} → A

    -- import Algebra.RingSolver
    -- open module ℝ-Solver = Algebra.RingSolver CoeffRing ACR-ℝ casts
  
  *-test-rs : ∀ (ε : ℝ) → nils ε → ε * ε ≡ 0#
  *-test-rs ε Δε = solve 0 (con (Sε.ε*+ 1) :* con (Sε.ε*+ 1) := con (Sε.ε*+ 0)) refl where
    module Sε = CoeffsWith ε Δε
    import Algebra.RingSolver
    open module ℝ-Solver = Algebra.RingSolver Sε.CoeffRing Sε.ACR-ℝ Sε.casts

  mixed : ∀ {x : ℝ} → 0# * x + 0# ≡ 0#
  mixed {x} =
    begin
      0# * x + 0#
    ≡⟨ cong₂ _+_ (proj₁ zero x) refl ⟩
      0# + 0#
    ≡⟨ proj₁ +-identity 0# ⟩
      0# ∎

  mixed-2 : ∀ {x y : ℝ} → (0# * y + 0#) * x + (0# * y + 0#) ≡ 0#
  mixed-2 {x} {y} = 
    begin
      (0# * y + 0#) * x + (0# * y + 0#)
    ≡⟨ cong (λ φ → φ * x + φ) mixed ⟩
      0# * x + 0#
    ≡⟨ mixed ⟩
      0#
    ∎

  *-test2-rs : ∀ (ε : ℝ) → nils ε → ∀ (a : ℝ) → (ε * ε) * a ≡ 0#
  *-test2-rs ε Δε = solve 1 (λ a → (con (ε*+ 1) :* con (ε*+ 1)) :* a := con (ε*+ 0)) mixed where
    open module Sε = CoeffsWith ε Δε
    import Algebra.RingSolver
    open module ℝ-Solver = Algebra.RingSolver Sε.CoeffRing Sε.ACR-ℝ Sε.casts
    

  *-test3-rs : ∀ (ε : ℝ) → nils ε → ∀ (a : ℝ) → ε * (a * ε) ≡ 0#
  *-test3-rs ε Δε = solve 1 (λ a → con (ε*+ 1) :* (a :* con (ε*+ 1)) := con (ε*+ 0)) mixed where
    open module Sε = CoeffsWith ε Δε
    import Algebra.RingSolver
    open module ℝ-Solver = Algebra.RingSolver Sε.CoeffRing Sε.ACR-ℝ Sε.casts

  *-test4-rs : ∀ (ε : ℝ) → nils ε → ∀ (a b : ℝ) → (ε * a) * (ε * b) ≡ 0#
  *-test4-rs ε Δε = solve 2
                      (λ a b → (con (ε*+ 1) :* a) :* (con (ε*+ 1) :* b)
                               := con (ε*+ 0)
                      )
                      mixed-2 where
    open module Sε = CoeffsWith ε Δε
    import Algebra.RingSolver
    open module ℝ-Solver = Algebra.RingSolver Sε.CoeffRing Sε.ACR-ℝ Sε.casts

  *-test5-rs : ∀ (ε : ℝ) → nils ε → (ε + ε) * (ε + ε) ≡ 0#
  *-test5-rs ε Δε = solve 0 ((con (ε*+ 1) :+ con (ε*+ 1)) :* (con (ε*+ 1) :+ con (ε*+ 1)) := con (ε*+ 0)) refl  where
    open module Sε = CoeffsWith ε Δε
    import Algebra.RingSolver
    open module ℝ-Solver = Algebra.RingSolver Sε.CoeffRing Sε.ACR-ℝ Sε.casts

  +-absorb : ∀ (x y : ℝ) → ~ x + (x + y) ≡ y
  +-absorb x y =
    begin
      ~ x + (x + y)
    ≡⟨ sym (+-assoc (~ x) x y) ⟩
      (~ x + x) + y
    ≡⟨ cong (λ P → P + y) (proj₁ +-inverse x) ⟩
      0# + y
    ≡⟨ proj₁ +-identity y ⟩
      y
    ∎

  +-cancel : ∀ (a b c : ℝ) → a + b ≡ a + c → b ≡ c
  +-cancel a b c a+b≡a+c = begin
    b
      ≡⟨ sym (proj₁ +-identity b) ⟩
    0# + b
      ≡⟨ cong (λ p → p + b) (sym (proj₁ +-inverse a)) ⟩
    (~ a + a) + b
      ≡⟨ +-assoc (~ a) a b ⟩
    ~ a + (a + b)
      ≡⟨ cong (λ p → ~ a + p) a+b≡a+c ⟩
    ~ a + (a + c)
      ≡⟨ sym (+-assoc (~ a) a c) ⟩
    (~ a + a) + c
      ≡⟨ cong (λ p → p + c) (proj₁ +-inverse a) ⟩
    0# + c
      ≡⟨ proj₁ +-identity c ⟩
    c ∎

  -- Multiplication lemma for nilsquares
  -- The left-left case is enough, the others reduce to this by commutativity
  *-nils : ∀ (a b : ℝ) → ∀ (ε : ℝ) → nils ε →
              (ε * a) * (ε * b) ≡ 0#
  *-nils a b ε Δε = begin
      (ε * a) * (ε * b)
    ≡⟨ *-assoc ε a (ε * b) ⟩
      ε * (a * (ε * b))
    ≡⟨ cong (λ P → ε * P) (sym (*-assoc a ε b)) ⟩
      ε * ((a * ε) * b)
    ≡⟨ cong (λ P → ε * (P * b)) (*-comm a ε) ⟩
      ε * ((ε * a) * b)
    ≡⟨ cong (λ P → ε * P) (*-assoc ε a b) ⟩
      ε * (ε * (a * b))
    ≡⟨ sym (*-assoc ε ε (a * b)) ⟩
      ε * ε * (a * b)
    ≡⟨ cong (λ P → P * (a * b)) Δε ⟩
      0# * (a * b)
    ≡⟨ proj₁ zero (a * b) ⟩
      0#
    ∎


-- the Microcancellation theorem
  microcancellation : ∀ (a b : ℝ) →
                      (∀ (ε : ℝ) → nils ε → ε * a ≡ ε * b) →
                      a ≡ b
  microcancellation a b premise = der#-unique f a b lhs rhs where
    f : ℝ → ℝ
    f x = x * a
    lhs : ∀ (ε : ℝ) → nils ε → f ε ≡ f 0# + ε * a
    lhs ε Δε = begin
        ε * a
      ≡⟨ sym (proj₁ +-identity (ε * a)) ⟩
        0# + ε * a
      ≡⟨ cong (λ P → P + ε * a) (sym (proj₁ zero a)) ⟩
        f 0# + ε * a
      ∎
    rhs : ∀ (ε : ℝ) → nils ε → f ε ≡ f 0# + ε * b
    rhs ε Δε = begin
        f ε
      ≡⟨ lhs ε Δε ⟩
        f 0# + ε * a
      ≡⟨ cong (λ P → f 0# + P) (premise ε Δε) ⟩
        f 0# + ε * b
      ∎