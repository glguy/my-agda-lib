open import Algebra using (Semigroup; module Semigroup)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup)
open import Data.List.NonEmpty
open import Data.Product using (proj₁; proj₂)
open import Level using (Level)
open import Function

module Algebra.SemigroupSolver {a ℓ : Level} (semigroup : Semigroup a ℓ) where

open Semigroup semigroup

open import Relation.Binary.EqReasoning setoid

data Syntax (n : ℕ) : Set where
  _⊙_ : Syntax n → Syntax n → Syntax n
  var : Fin n → Syntax n

infixl 7 _⊙_

-- This semantic evaluation function constructs a value
-- of Carrier which preserves the shape of the Syntax
-- tree. This is the shape of the proof we want to have.

⟦_⟧ : {n : ℕ} → Syntax n → Vec Carrier n → Carrier
⟦ x₁ ⊙ x₂ ⟧ ρ = ⟦ x₁ ⟧ ρ ∙ ⟦ x₂ ⟧ ρ
⟦ var i   ⟧ ρ = lookup i ρ

private
  normalize : {n : ℕ} → Syntax n → Vec Carrier n → List⁺ Carrier
  normalize (x₁ ⊙ x₂) ρ = normalize x₁ ρ ⁺++⁺ normalize x₂ ρ
  normalize (var i)   ρ = [ lookup i ρ ]

  sum : List⁺ Carrier → Carrier
  sum = foldr _∙_ id

-- This normalized semantic evaluation function constructs a
-- value of Carrier which is semantically equivalent to the
-- one produced by ⟦_⟧, however all occurences of _∙_ are
-- made right-associative and all ε elements are eliminated.
-- This is the shape of the proof we want to provide.

⟦_⇓⟧ : {n : ℕ} → Syntax n → Vec Carrier n → Carrier
⟦ x ⇓⟧ ρ = sum (normalize x ρ)

private
  sum-++ : (xs ys : List⁺ Carrier) → sum (xs ⁺++⁺ ys) ≈ sum xs ∙ sum ys
  sum-++ [ x ] [ y ] = refl
  sum-++ [ x ] (y ∷ ys) = refl
  sum-++ (x ∷ xs) ys = begin
    x ∙  sum (xs ⁺++⁺ ys)   ≈⟨ ∙-cong refl (sum-++ xs ys) ⟩
    x ∙ (sum xs ∙ sum ys) ≈⟨ sym (assoc _ _ _) ⟩
    x ∙  sum xs ∙ sum ys  ∎

-- By proving that these two semantic evaluation functions produce
-- semantically equivalent values we'll be able to use equivalence
-- proofs about the normalized forms to talk about the equivalence
-- of the original values.

correct : {n : ℕ} (s : Syntax n) (ρ : Vec Carrier n) → ⟦ s ⇓⟧ ρ ≈ ⟦ s ⟧ ρ
correct (var i)   ρ = refl
correct (x₁ ⊙ x₂) ρ = begin
   ⟦ x₁      ⊙  x₂ ⇓⟧ ρ ≈⟨ sum-++ (normalize x₁ ρ) (normalize x₂ ρ) ⟩
   ⟦ x₁ ⇓⟧ ρ ∙ ⟦ x₂ ⇓⟧ ρ ≈⟨ ∙-cong (correct x₁ ρ) (correct x₂ ρ) ⟩
   ⟦ x₁  ⟧ ρ ∙ ⟦ x₂  ⟧ ρ ∎ 

import Relation.Binary.Reflection as R
open R setoid var ⟦_⟧ ⟦_⇓⟧ correct public using (prove; close; solve; solve₁; _⊜_)

private
  -- Now for a simple example
  Example = ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≈ a ∙ (b ∙ c) ∙ d

  -- A manual proof using equational reasoning looks like this.
  manual : Example
  manual a b c d = begin
    (a ∙ b) ∙ (c ∙ d) ≈⟨ sym (assoc (a ∙ b) c d) ⟩
     a ∙ b  ∙  c ∙ d  ≈⟨ ∙-cong (assoc a b c) refl ⟩
     a ∙ (b ∙ c) ∙ d  ∎

  -- Let's see the solver in action!
  automatic : Example
  automatic = solve 4 (λ a b c d → (a ⊙ b) ⊙ (c ⊙ d) ⊜ a ⊙ (b ⊙ c) ⊙ d) refl
                                -- ^ Here we reflect the shape of the proof we want
