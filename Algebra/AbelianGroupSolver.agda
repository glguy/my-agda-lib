open import Algebra using (module AbelianGroup; AbelianGroup; module CommutativeRing)

module Algebra.AbelianGroupSolver {a ℓ} (C : AbelianGroup a ℓ) where

open AbelianGroup C

open import Data.Fin     using (Fin; suc; zero)
open import Data.Vec     using (Vec; _∷_; []; lookup; replicate; zipWith; map)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; -_)
open import Data.Nat as ℕ using (ℕ; _+_; suc; zero)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.EqReasoning setoid
open import Algebra.Group.Exponentiation group
open import Function using (_⟨_⟩_)
open import Algebra.CommutativeMonoidSolver commutativeMonoid using (solve; _⊜_) renaming (_⊕_ to _⊙_)
open import Algebra.Props.Group group
import Algebra.Props.AbelianGroup as AG
open AG C using (⁻¹-∙-comm)

data Expr (n : ℕ) : Set where
  _⊕_ : (x₁ x₂ : Expr n) → Expr n
  :0  : Expr n
  var : (x : Fin n) → Expr n
  inv : (x : Expr n) → Expr n

private
  Env = Vec Carrier
  Normal = Vec ℤ

  ⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
  ⟦ x₁ ⊕ x₂ ⟧ ρ = ⟦ x₁ ⟧ ρ ∙ ⟦ x₂ ⟧ ρ
  ⟦ var x   ⟧ ρ = lookup x ρ
  ⟦ :0      ⟧ _ = ε
  ⟦ inv x   ⟧ ρ = (⟦ x ⟧ ρ) ⁻¹

  ∙-NF : {n : ℕ} → Normal n → Normal n → Normal n
  ∙-NF = zipWith ℤ._+_

  var-NF : {n : ℕ} → Fin n → Normal n
  var-NF zero    = + 1 ∷ replicate (+ 0)
  var-NF (suc i) = + 0 ∷ var-NF i

  inv-NF : {n : ℕ} → Normal n → Normal n
  inv-NF = Data.Vec.map -_

  ε-NF : {n : ℕ} → Normal n
  ε-NF = replicate (+ 0)

  normalize : {n : ℕ} → Expr n → Normal n
  normalize (x₁ ⊕ x₂) = ∙-NF (normalize x₁) (normalize x₂)
  normalize (var x)   = var-NF x
  normalize :0        = ε-NF
  normalize (inv x)   = inv-NF (normalize x)

  ⟦_⟧-Normal : {n : ℕ} → Normal n → Env n → Carrier
  ⟦_⟧-Normal [] _ = ε
  ⟦_⟧-Normal (n ∷ ns) (x ∷ ρ) = x ^ n ∙ ⟦ ns ⟧-Normal ρ

  ⟦⟧-Normal-∙-NF-comm : {n : ℕ} (x₁ x₂ : Normal n) (ρ : Env n) →
               ⟦ ∙-NF x₁ x₂ ⟧-Normal ρ ≈ ⟦ x₁ ⟧-Normal ρ ∙ ⟦ x₂ ⟧-Normal ρ
  ⟦⟧-Normal-∙-NF-comm [] [] _ = sym (proj₂ identity ε)
  ⟦⟧-Normal-∙-NF-comm (x ∷ xs) (y ∷ ys) (v ∷ ρ) = begin
     ⟦ ∙-NF (x ∷ xs) (y ∷ ys) ⟧-Normal (v ∷ ρ)

           ≈⟨ sym (exp-plus v x y) ⟨ ∙-cong ⟩ ⟦⟧-Normal-∙-NF-comm xs ys ρ ⟩

     (v ^ x ∙ v ^ y) ∙ (⟦ xs ⟧-Normal ρ ∙ ⟦ ys ⟧-Normal ρ)

           ≈⟨ solve 4 (λ a₁ b c d → (a₁ ⊙ b) ⊙ (c ⊙ d) ⊜ (a₁ ⊙ c) ⊙ (b ⊙ d))
                refl (v ^ x) (v ^ y) _ _ ⟩

     ⟦ x ∷ xs ⟧-Normal (v ∷ ρ) ∙ ⟦ y ∷ ys ⟧-Normal (v ∷ ρ)
           ∎

  ⟦_⇓⟧ : {n : ℕ} → Expr n → Env n → Carrier
  ⟦ x ⇓⟧ = ⟦ normalize x ⟧-Normal

  correct-ε : {n : ℕ} (ρ : Env n) → ⟦ :0 ⇓⟧ ρ ≈ ⟦ :0 ⟧ ρ
  correct-ε []      = refl
  correct-ε (x ∷ ρ) = begin
    ⟦ :0 ⇓⟧ (x ∷ ρ) ≈⟨ proj₁ identity _ ⟩
    ⟦ :0 ⇓⟧      ρ  ≈⟨ correct-ε ρ ⟩
    ⟦ :0  ⟧ (x ∷ ρ) ∎

  correct-var : {n : ℕ} (x : Fin n) (ρ : Env n) → ⟦ var x ⇓⟧ ρ ≈ ⟦ var x ⟧ ρ
  correct-var zero (x ∷ ρ) = begin
    ⟦ var zero     ⇓⟧ (x ∷ ρ) ≈⟨ proj₂ identity x ⟨ ∙-cong ⟩ correct-ε ρ ⟩
    ⟦ var zero ⊕ :0 ⟧ (x ∷ ρ) ≈⟨ proj₂ identity x ⟩
    ⟦ var zero      ⟧ (x ∷ ρ) ∎
  correct-var (suc i) (x ∷ ρ) = begin
    ⟦ var (suc i)  ⇓⟧ (x ∷ ρ) ≈⟨ proj₁ identity _ ⟩
    ⟦ var i        ⇓⟧      ρ  ≈⟨ correct-var i ρ ⟩
    ⟦ var (suc i)   ⟧ (x ∷ ρ) ∎

  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  map-lift-involutive : ∀ {A : Set} {n : ℕ} (f : A → A) (x : Vec A n) →
                         (∀ x → f (f x) ≡ x) →
                          map f (map f x) ≡ x
  map-lift-involutive f [] invol = ≡.refl
  map-lift-involutive f (x ∷ x₁) invol = ≡.cong₂ _∷_ (invol x) (map-lift-involutive f x₁ invol)

  negation-involutive : (x : ℤ) → - (- x) ≡ x
  negation-involutive -[1+ n ]  = ≡.refl
  negation-involutive (+ zero)  = ≡.refl
  negation-involutive (+ suc n) = ≡.refl

  inverse-unit : ε ≈ ε ⁻¹
  inverse-unit = begin
     ε ≈⟨ sym (proj₂ inverse ε) ⟩
     (ε ∙ ε ⁻¹) ≈⟨ proj₁ identity _ ⟩
     ε ⁻¹ ∎

  negate-zeros : (n : ℕ) → inv-NF (ε-NF {n = n}) ≡ ε-NF
  negate-zeros zero = ≡.refl
  negate-zeros (suc n) = ≡.cong₂ _∷_ ≡.refl (negate-zeros n)

  invNF-∙-NF-comm : {n : ℕ} (x y : Vec ℤ n) → inv-NF (∙-NF x y) ≡ ∙-NF (inv-NF x) (inv-NF y)
  invNF-∙-NF-comm [] [] = ≡.refl
  invNF-∙-NF-comm (x ∷ x₁) (x₂ ∷ y) = ≡.cong₂ _∷_ (≡.sym (f x x₂)) (invNF-∙-NF-comm x₁ y)
    where
    import Data.Integer.Properties as P
    open AG (CommutativeRing.+-abelianGroup P.commutativeRing) renaming (⁻¹-∙-comm to f)

  correct : {n : ℕ} (e : Expr n) (ρ : Env n) → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
  correct-⊕ : {n : ℕ} (x₁ x₂ : Expr n) (ρ : Env n) → ⟦ x₁ ⊕ x₂ ⇓⟧ ρ ≈ ⟦ x₁ ⊕ x₂ ⟧ ρ

  correct-inv : {n : ℕ} (x : Expr n) (ρ : Env n) → ⟦ inv x ⇓⟧ ρ ≈ ⟦ inv x ⟧ ρ
  correct-inv (x ⊕ x₁) ρ = begin
    ⟦ inv    (x ⊕ x₁)     ⇓⟧ ρ ≡⟨ invNF-∙-NF-comm (normalize x) (normalize x₁) ⟨ ≡.cong₂ ⟦_⟧-Normal ⟩ ≡.refl ⟩
    ⟦ inv x     ⊕  inv x₁ ⇓⟧ ρ ≈⟨ correct-⊕ (inv x) (inv x₁) ρ ⟩
    ⟦ inv x ⟧ ρ ∙ ⟦ inv x₁ ⟧ ρ ≈⟨ ⁻¹-∙-comm (⟦ x ⟧ ρ) (⟦ x₁ ⟧ ρ) ⟩
    ⟦ inv    (x ⊕ x₁)      ⟧ ρ ∎
  correct-inv :0 [] = inverse-unit
  correct-inv :0 (x ∷ ρ) = trans (proj₁ identity _) (correct-inv :0 ρ)
  correct-inv {suc n} (var zero) (x ∷ ρ) = begin
    ⟦ inv (var zero)     ⇓⟧ (x ∷ ρ)             ≡⟨ ≡.refl ⟨ ≡.cong₂ _∙_ ⟩ (negate-zeros n ⟨ ≡.cong₂ ⟦_⟧-Normal ⟩ ≡.refl) ⟩
    ⟦ inv (var zero) ⊕ :0 ⟧ (x ∷ ρ) ∙ ⟦ :0 ⇓⟧ ρ ≈⟨ proj₂ identity _ ⟨ ∙-cong ⟩ correct-ε ρ ⟩
    ⟦ inv (var zero)      ⟧ (x ∷ ρ) ∙ ⟦ :0  ⟧ ρ ≈⟨ proj₂ identity _ ⟩
    ⟦ inv (var zero)      ⟧ (x ∷ ρ) ∎
  correct-inv (var (suc x)) (x₁ ∷ ρ) = trans (proj₁ identity _) (correct-inv (var x) ρ)
  correct-inv (inv x) ρ = begin
    ⟦ inv (inv x) ⇓⟧ ρ ≡⟨ ≡.cong₂ ⟦_⟧-Normal (map-lift-involutive -_ (normalize x) negation-involutive) ≡.refl ⟩
    ⟦ x           ⇓⟧ ρ ≈⟨ correct x ρ ⟩
    ⟦ x            ⟧ ρ ≈⟨ sym (⁻¹-involutive (⟦ x ⟧ ρ)) ⟩
    ⟦ inv (inv x)  ⟧ ρ ∎

  correct-⊕ x₁ x₂ ρ = begin
     ⟦ x₁      ⊕   x₂ ⇓⟧ ρ ≈⟨ ⟦⟧-Normal-∙-NF-comm (normalize x₁) (normalize x₂) ρ ⟩
     ⟦ x₁ ⇓⟧ ρ ∙ ⟦ x₂ ⇓⟧ ρ ≈⟨ ∙-cong (correct x₁ ρ) (correct x₂ ρ) ⟩
     ⟦ x₁  ⟧ ρ ∙ ⟦ x₂  ⟧ ρ ∎

  correct (var x)   = correct-var x
  correct :0        = correct-ε
  correct (x₁ ⊕ x₂) = correct-⊕ x₁ x₂
  correct (inv x)   = correct-inv x

import Relation.Binary.Reflection as R
open R setoid var ⟦_⟧ ⟦_⇓⟧ correct public
