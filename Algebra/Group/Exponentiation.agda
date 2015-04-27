open import Data.Integer
open import Data.Nat hiding (_+_)
open import Algebra
import Relation.Binary.EqReasoning
import Algebra.MonoidSolver
open import Data.Product
open import Function

module Algebra.Group.Exponentiation {c ℓ} (G : Group c ℓ) where


  open Group G
  open Relation.Binary.EqReasoning setoid
  open Algebra.MonoidSolver monoid

  _^-ℕ_ : Carrier → ℕ → Carrier
  x ^-ℕ zero = ε
  x ^-ℕ ℕ.suc n = x ∙ x ^-ℕ n

  infixl 8 _^-ℕ_

  _^_ : Carrier → ℤ → Carrier
  x ^ -[1+ n ] = (x ⁻¹) ^-ℕ (ℕ.suc n)
  x ^ (+ n) = x ^-ℕ n

  simplify-right′ : ∀ x n → x ^-ℕ (ℕ.suc n) ≈ (x ^-ℕ n) ∙ x
  simplify-right′ x zero = begin
     x ∙ ε ≈⟨ proj₂ identity _ ⟩
     x ≈⟨ sym (proj₁ identity _) ⟩
     ε ∙ x ∎
  simplify-right′ x (ℕ.suc n) = begin
    x ∙ (x ∙ x ^-ℕ n) ≈⟨ refl ⟨ ∙-cong ⟩ simplify-right′ x n ⟩
    x ∙ (x ^-ℕ n ∙ x) ≈⟨ sym (assoc _ _ _) ⟩
    x ∙ x ^-ℕ n ∙ x ∎

  exp-plus′ : ∀ x i j → (x ^-ℕ i) ∙ (x ^-ℕ j) ≈ (x ^-ℕ (Data.Nat._+_ i j))
  exp-plus′ x zero j = proj₁ identity _
  exp-plus′ x (ℕ.suc n) j = trans (assoc _ _ _) (refl ⟨ ∙-cong ⟩ exp-plus′ x n j)

  exp-minus′ : ∀ x i j → x ^-ℕ i ∙ (x ⁻¹) ^-ℕ j ≈ x ^ (i ⊖ j)
  exp-minus′ x zero zero = proj₁ identity _
  exp-minus′ x zero (ℕ.suc n) = proj₁ identity _
  exp-minus′ x (ℕ.suc n) zero = proj₂ identity _
  exp-minus′ x (ℕ.suc n) (ℕ.suc n') = begin
    x ^-ℕ (ℕ.suc n) ∙ ((x ⁻¹) ∙ (x ⁻¹) ^-ℕ n') ≈⟨ simplify-right′ x n ⟨ ∙-cong ⟩ refl ⟩
    (x ^-ℕ n) ∙ x ∙ (x ⁻¹ ∙ (x ⁻¹) ^-ℕ n') ≈⟨ solve 4 (λ a b c' d → a ⊙ b ⊙ (c' ⊙ d) ⊜ a ⊙ (b ⊙ c') ⊙ d) refl _ _
                                                _ _ ⟩
    (x ^-ℕ n ∙ (x ∙ x ⁻¹) ∙ (x ⁻¹) ^-ℕ n') ≈⟨ refl ⟨ ∙-cong ⟩ proj₂ inverse _ ⟨ ∙-cong ⟩ refl ⟩
    (x ^-ℕ n ∙ ε ∙ (x ⁻¹) ^-ℕ n') ≈⟨ proj₂ identity _ ⟨ ∙-cong ⟩ refl ⟩
    (x ^-ℕ n ∙ (x ⁻¹) ^-ℕ n') ≈⟨ exp-minus′ x n n' ⟩
    x ^ (n ⊖ n') ∎

  exp-swap : ∀ x i j → (x ⁻¹) ^-ℕ i ∙ x ^-ℕ j ≈ x ^-ℕ j ∙ (x ⁻¹) ^-ℕ i
  exp-swap x zero j = trans (proj₁ identity _) (sym (proj₂ identity _))
  exp-swap x n zero = trans (proj₂ identity _) (sym (proj₁ identity _))
  exp-swap x (ℕ.suc n) (ℕ.suc n') = begin
     x ⁻¹ ∙ (x ⁻¹) ^-ℕ n ∙ (x ∙ x ^-ℕ n') ≈⟨ simplify-right′ (x ⁻¹) n ⟨ ∙-cong ⟩ refl ⟩
     (x ⁻¹) ^-ℕ n ∙ x ⁻¹ ∙ (x ∙ x ^-ℕ n') ≈⟨ solve 4 (λ a b c' d → a ⊙ b ⊙ (c' ⊙ d) ⊜ a ⊙ (b ⊙ c') ⊙ d) refl _ _
                                               _ _ ⟩
     (x ⁻¹) ^-ℕ n ∙ (x ⁻¹ ∙ x) ∙ x ^-ℕ n' ≈⟨ refl ⟨ ∙-cong ⟩ proj₁ inverse _ ⟨ ∙-cong ⟩ refl ⟩
     (x ⁻¹) ^-ℕ n ∙ ε ∙ x ^-ℕ n' ≈⟨ proj₂ identity _ ⟨ ∙-cong ⟩ refl ⟩
     (x ⁻¹) ^-ℕ n ∙ x ^-ℕ n' ≈⟨ exp-swap x n n' ⟩
     x ^-ℕ n' ∙ (x ⁻¹) ^-ℕ n ≈⟨ sym (proj₂ identity _) ⟨ ∙-cong ⟩ refl ⟩
     x ^-ℕ n' ∙ ε ∙ (x ⁻¹) ^-ℕ n ≈⟨ refl ⟨ ∙-cong ⟩ sym (proj₂ inverse _) ⟨ ∙-cong ⟩ refl ⟩
     x ^-ℕ n' ∙ (x ∙ x ⁻¹) ∙ (x ⁻¹) ^-ℕ n ≈⟨ solve 4 (λ a b c' d → a ⊙ (b ⊙ c') ⊙ d ⊜ a ⊙ b ⊙ (c' ⊙ d)) refl _ _
                                               _ _ ⟩
     x ^-ℕ n' ∙ x ∙ (x ⁻¹ ∙ (x ⁻¹) ^-ℕ n) ≈⟨ sym (simplify-right′ x n') ⟨ ∙-cong ⟩ refl ⟩
      x ∙ x ^-ℕ n' ∙ (x ⁻¹ ∙ (x ⁻¹) ^-ℕ n) ∎

  exp-plus : ∀ x i j → x ^ i ∙ x ^ j ≈ x ^ (i + j)
  exp-plus x -[1+ n ] -[1+ n' ] = trans (assoc _ _ _) (∙-cong refl (trans (sym (assoc _ _ _)) (trans (sym (simplify-right′ (x ⁻¹) n) ⟨ ∙-cong ⟩ refl) (trans (assoc _ _ _) (refl ⟨ ∙-cong ⟩ exp-plus′ (x ⁻¹) n n')))))
  exp-plus x -[1+ n ] (+ n') = trans (exp-swap x (ℕ.suc n) n') (exp-minus′ x n' (ℕ.suc n))
  exp-plus x (+ zero) -[1+ n' ] = proj₁ identity _
  exp-plus x (+ ℕ.suc n) -[1+ n' ] = exp-minus′ x (ℕ.suc n) (ℕ.suc n')
  exp-plus x (+ i) (+ j) = exp-plus′ x i j

  inv-push : ∀ a b → (a ∙ b) ⁻¹ ≈ b ⁻¹ ∙ a ⁻¹
  inv-push a b = begin 
    (a ∙ b) ⁻¹ ≈⟨ sym (proj₂ identity _) ⟩
    (a ∙ b) ⁻¹ ∙ ε ≈⟨ refl ⟨ ∙-cong ⟩ sym (proj₂ inverse _) ⟩
    (a ∙ b) ⁻¹ ∙ (a ∙ a ⁻¹) ≈⟨ refl ⟨ ∙-cong ⟩ (sym (proj₂ identity _) ⟨ ∙-cong ⟩ refl) ⟩
    (a ∙ b) ⁻¹ ∙ (a ∙ ε ∙ a ⁻¹) ≈⟨ refl ⟨ ∙-cong ⟩ (refl ⟨ ∙-cong ⟩ sym (proj₂ inverse _) ⟨ ∙-cong ⟩ refl) ⟩
    (a ∙ b) ⁻¹ ∙ (a ∙ (b ∙ b ⁻¹) ∙ a ⁻¹) ≈⟨ solve 5
                                              (λ x x′ y y′ z → z ⊙ (x ⊙ (y ⊙ y′) ⊙ x′) ⊜ z ⊙ (x ⊙ y) ⊙ (y′ ⊙ x′))
                                              refl _ _ _ _ _ ⟩
    (a ∙ b) ⁻¹ ∙ (a ∙ b) ∙ (b ⁻¹ ∙ a ⁻¹) ≈⟨ proj₁ inverse _ ⟨ ∙-cong ⟩ refl ⟩
    ε ∙ (b ⁻¹ ∙ a ⁻¹) ≈⟨ proj₁ identity _ ⟩
    b ⁻¹ ∙ a ⁻¹ ∎

  ^-ℕ-cong : ∀ {x y} n → x ≈ y → x ^-ℕ n ≈ y ^-ℕ n
  ^-ℕ-cong zero eq = refl
  ^-ℕ-cong (ℕ.suc n) eq = eq ⟨ ∙-cong ⟩ ^-ℕ-cong n eq


  simplify-left : ∀ x n → x ^ (Data.Integer.suc n) ≈ x ∙ x ^ n
  simplify-left x n = trans (sym (exp-plus x (+ 1) n)) (proj₂ identity _ ⟨ ∙-cong ⟩ refl)

  simplify-right : ∀ x n → x ^ (Data.Integer.suc n) ≈ x ^ n ∙ x
  simplify-right x -[1+ n ] = trans (sym (exp-minus′ x 0 n)) (trans (proj₁ identity _) (trans (trans (trans (sym (proj₂ identity _)) (refl ⟨ ∙-cong ⟩ sym (proj₁ inverse _))) (sym (assoc _ _ _))) (sym (simplify-right′ (x ⁻¹) n) ⟨ ∙-cong ⟩ refl)))
  simplify-right x (+ n) = simplify-right′ x n

  simplify-pair′ : ∀ n a b → (a ∙ b) ^-ℕ (ℕ.suc n) ≈ a ∙ (b ∙ a) ^-ℕ n ∙ b
  simplify-pair′ zero a b = begin
     a ∙ b ∙ ε ≈⟨ proj₂ identity _ ⟩
     a ∙ b ≈⟨ sym (proj₂ identity _) ⟨ ∙-cong ⟩ refl ⟩
     a ∙ ε ∙ b ∎
  simplify-pair′ (ℕ.suc n) a b = begin
     a ∙ b ∙ (a ∙ b ∙ (a ∙ b) ^-ℕ n) ≈⟨ refl ⟨ ∙-cong ⟩ simplify-pair′ n a b ⟩
     a ∙ b ∙ (a ∙ (b ∙ a) ^-ℕ n ∙ b) ≈⟨ solve 3 (λ x y z → x ⊙ y ⊙ (x ⊙ z ⊙ y) ⊜ x ⊙ (y ⊙ x ⊙ z) ⊙ y) refl
                                          _ _ _ ⟩
     a ∙ (b ∙ a ∙ (b ∙ a) ^-ℕ n) ∙ b ∎

  simplify-pair : ∀ n a b → (a ∙ b) ^ Data.Integer.suc n ≈ a ∙ (b ∙ a) ^ n ∙ b
  simplify-pair -[1+ zero ] a b = begin
    ε ≈⟨ sym (proj₁ identity _) ⟩
    ε ∙ ε ≈⟨ sym (proj₂ inverse _ ⟨ ∙-cong ⟩ proj₁ inverse _) ⟩ 
    (a ∙ a ⁻¹) ∙ (b ⁻¹ ∙ b) ≈⟨ solve 4 (λ a' b' c' d → a' ⊙ b' ⊙ (c' ⊙ d) ⊜ a' ⊙ (b' ⊙ c') ⊙ d)
                                 refl _ _ _ _ ⟩ 
    a ∙ (a ⁻¹ ∙ b ⁻¹) ∙ b ≈⟨ refl ⟨ ∙-cong ⟩ sym (inv-push b a) ⟨ ∙-cong ⟩ refl ⟩ 
    a ∙ (b ∙ a) ⁻¹ ∙ b ≈⟨ refl ⟨ ∙-cong ⟩ sym (proj₂ identity _) ⟨ ∙-cong ⟩ refl ⟩ 
    a ∙ ((b ∙ a) ⁻¹ ∙ ε) ∙ b ∎

  simplify-pair -[1+ ℕ.suc n ] a b = begin
    (a ∙ b) ⁻¹ ∙ ((a ∙ b) ⁻¹) ^-ℕ n ≈⟨ ^-ℕ-cong (ℕ.suc n) (inv-push a b) ⟩
    (b ⁻¹ ∙ a ⁻¹) ^-ℕ (ℕ.suc n) ≈⟨ simplify-pair′ n (b ⁻¹) (a ⁻¹) ⟩
    b ⁻¹ ∙ (a ⁻¹ ∙ b ⁻¹) ^-ℕ n ∙ a ⁻¹ ≈⟨ refl ⟨ ∙-cong ⟩ ^-ℕ-cong n (sym (inv-push b a)) ⟨ ∙-cong ⟩ refl ⟩
    b ⁻¹ ∙ ((b ∙ a) ⁻¹) ^-ℕ n ∙ a ⁻¹ ≈⟨ sym (proj₁ identity _) ⟩
    ε ∙ (b ⁻¹ ∙ ((b ∙ a) ⁻¹) ^-ℕ n ∙ a ⁻¹) ≈⟨ sym (proj₂ identity _) ⟩
    ε ∙ (b ⁻¹ ∙ ((b ∙ a) ⁻¹) ^-ℕ n ∙ a ⁻¹) ∙ ε ≈⟨ sym (proj₂ inverse _ ⟨ ∙-cong ⟩ refl ⟨ ∙-cong ⟩ proj₁ inverse _) ⟩
    (a ∙ a ⁻¹) ∙ (b ⁻¹ ∙ ((b ∙ a) ⁻¹) ^-ℕ n ∙ a ⁻¹) ∙ (b ⁻¹ ∙ b) ≈⟨ solve 5
                                                                      (λ x x′ y y′ z →
                                                                         x ⊙ x′ ⊙ (y′ ⊙ z ⊙ x′) ⊙ (y′ ⊙ y) ⊜
                                                                         x ⊙ (x′ ⊙ y′ ⊙ (z ⊙ (x′ ⊙ y′))) ⊙ y)
                                                                      refl a (a ⁻¹) b (b ⁻¹) _ ⟩
    a ∙ (a ⁻¹ ∙ b ⁻¹ ∙ (((b ∙ a) ⁻¹) ^-ℕ n ∙ (a ⁻¹ ∙ b ⁻¹))) ∙ b ≈⟨ ∙-cong (∙-cong refl (∙-cong refl (∙-cong refl (sym (inv-push b a))))) refl ⟩
    a ∙ (a ⁻¹ ∙ b ⁻¹ ∙ (((b ∙ a) ⁻¹) ^-ℕ n ∙ (b ∙ a) ⁻¹)) ∙ b ≈⟨ ∙-cong (∙-cong refl (∙-cong (sym (inv-push b a)) (sym (simplify-right′ ((b ∙ a) ⁻¹) n)))) refl ⟩
    a ∙ ((b ∙ a) ⁻¹ ∙ ((b ∙ a) ⁻¹ ∙ ((b ∙ a) ⁻¹) ^-ℕ n)) ∙ b ∎

  simplify-pair (+ zero) a b = solve 2 (λ x y → x ⊙ y ⊙ :0 ⊜ x ⊙ :0 ⊙ y) refl _ _
  simplify-pair (+ ℕ.suc n) a b =  begin
    a ∙ b ∙ ((a ∙ b) ^ (+ ℕ.suc n)) ≈⟨ ∙-cong refl (simplify-pair (+ n) _ _) ⟩
    a ∙ b ∙ (a ∙ (b ∙ a) ^ (+ n) ∙ b) ≈⟨ solve 3 (λ x y z → x ⊙ y ⊙ (x ⊙ z ⊙ y) ⊜ x ⊙ (y ⊙ x ⊙ z) ⊙ y) refl _ _ _ ⟩
      a ∙ (b ∙ a) ^ (+ ℕ.suc n) ∙ b ∎

  infixl 8 _^_
