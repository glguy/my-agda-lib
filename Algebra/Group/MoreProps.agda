open import Algebra using (Group; module Group)
open import Level using (Level)
open import Data.Product
open import Function

module Algebra.Group.MoreProps {a ℓ : Level} (group : Group a ℓ) where

open Group group

open import Relation.Binary.EqReasoning setoid
open import Algebra.MonoidSolver monoid

inverse-unit : ε ⁻¹ ≈ ε
inverse-unit = begin
       ε ⁻¹ ≈⟨ sym (proj₁ identity _) ⟩
   ε ∙ ε ⁻¹ ≈⟨ proj₂ inverse ε ⟩
   ε ∎

⁻¹-∙-comm : (x y : Carrier) → (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
⁻¹-∙-comm x y = begin
                         (x ∙ y) ⁻¹ ≈⟨ sym (proj₁ identity _) ⟩
   ε                    ∙ (x ∙ y) ⁻¹ ≈⟨ sym (proj₁ inverse _) ⟨ ∙-cong ⟩ refl ⟩
   (y ⁻¹            ∙ y) ∙ (x ∙ y) ⁻¹ ≈⟨ sym (proj₂ identity _) ⟨ ∙-cong ⟩ refl ⟨ ∙-cong ⟩ refl ⟩
   (y ⁻¹ ∙ ε         ∙ y) ∙ (x ∙ y) ⁻¹ ≈⟨ refl ⟨ ∙-cong ⟩ sym (proj₁ inverse _) ⟨ ∙-cong ⟩ refl ⟨ ∙-cong ⟩ refl ⟩
   (y ⁻¹ ∙ (x ⁻¹ ∙ x) ∙ y) ∙ (x ∙ y) ⁻¹ ≈⟨ solve 5
                                             (λ x₁ y₁ x′ y′ z →
                                                y′ ⊙ (x′ ⊙ x₁) ⊙ y₁ ⊙ z ⊜ y′ ⊙ (x′ ⊙ (x₁ ⊙ y₁ ⊙ z)))
                                             refl _ _ _ _ _ ⟩
   y ⁻¹ ∙ (x ⁻¹ ∙ (x ∙ y ∙ (x ∙ y) ⁻¹)) ≈⟨ refl ⟨ ∙-cong ⟩ (refl ⟨ ∙-cong ⟩ proj₂ inverse _) ⟩ 
   y ⁻¹ ∙ (x ⁻¹ ∙ ε) ≈⟨ refl ⟨ ∙-cong ⟩ proj₂ identity _ ⟩
   y ⁻¹ ∙ x ⁻¹ ∎
