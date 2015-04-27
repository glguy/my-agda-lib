open import Algebra using (module CommutativeMonoid; CommutativeMonoid)

module Algebra.CommutativeMonoidSolver {a ℓ} (C : CommutativeMonoid a ℓ) where

open CommutativeMonoid C

open import Data.Fin     using (Fin; suc; zero)
open import Data.Vec     using (Vec; _∷_; []; lookup; replicate; zipWith)
open import Data.Nat     using (ℕ; _+_; suc; zero)
open import Data.Product using (proj₂)
import Relation.Binary.EqReasoning as EqR
open EqR setoid

data Expr (n : ℕ) : Set where
  _⊕_ : (x₁ x₂ : Expr n) → Expr n
  :0   : Expr n
  var  : (x : Fin n) → Expr n

infixl 6 _⊕_

private
  Env = Vec Carrier
  Normal = Vec ℕ

  ⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
  ⟦ x₁ ⊕ x₂ ⟧ ρ = ⟦ x₁ ⟧ ρ ∙ ⟦ x₂ ⟧ ρ
  ⟦ var x   ⟧ ρ = lookup x ρ
  ⟦ :0      ⟧ _ = ε

  ∙-NF : {n : ℕ} → Normal n → Normal n → Normal n
  ∙-NF = zipWith _+_

  var-NF : {n : ℕ} → Fin n → Normal n
  var-NF zero    = 1 ∷ replicate 0
  var-NF (suc i) = 0 ∷ var-NF i

  ε-NF : {n : ℕ} → Normal n
  ε-NF = replicate 0

  normalize : {n : ℕ} → Expr n → Normal n
  normalize (x₁ ⊕ x₂) = ∙-NF (normalize x₁) (normalize x₂)
  normalize (var x)   = var-NF x
  normalize :0        = ε-NF

  ⟦_⟧-Normal : {n : ℕ} → Normal n → Env n → Carrier
  ⟦_⟧-Normal []           _       = ε
  ⟦_⟧-Normal (zero  ∷ ns) (_ ∷ ρ) =     ⟦ ns     ⟧-Normal ρ
  ⟦_⟧-Normal (suc n ∷ ns) (x ∷ ρ) = x ∙ ⟦ n ∷ ns ⟧-Normal (x ∷ ρ)

  ∙-NF-correct : {n : ℕ} (x₁ x₂ : Normal n) (ρ : Env n) →
       ⟦ ∙-NF x₁ x₂ ⟧-Normal ρ ≈ ⟦ x₁ ⟧-Normal ρ ∙ ⟦ x₂ ⟧-Normal ρ
  ∙-NF-correct []          []           _       = sym (proj₂ identity ε)
  ∙-NF-correct (zero ∷ xs) (zero  ∷ ys) (_ ∷ ρ) = ∙-NF-correct xs ys ρ
  ∙-NF-correct (zero ∷ xs) (suc n ∷ ys) (i ∷ ρ) = begin
    i ∙ ⟦ n ∷ ∙-NF xs ys ⟧-Normal (i ∷ ρ) ≈⟨ ∙-cong refl (∙-NF-correct (zero ∷ xs) (n ∷ ys) (i ∷ ρ)) ⟩
    i ∙ (⟦ zero ∷ xs ⟧-Normal (i ∷ ρ) ∙ ⟦ n ∷ ys ⟧-Normal (i ∷ ρ)) ≈⟨ sym (assoc _ _ _) ⟩
    i ∙ ⟦ zero ∷ xs ⟧-Normal (i ∷ ρ) ∙ ⟦ n ∷ ys ⟧-Normal (i ∷ ρ) ≈⟨ ∙-cong (comm _ _) refl ⟩
    ⟦ zero ∷ xs ⟧-Normal (i ∷ ρ) ∙ i ∙ ⟦ n ∷ ys ⟧-Normal (i ∷ ρ) ≈⟨ assoc _ _ _ ⟩
    ⟦ zero ∷ xs ⟧-Normal (i ∷ ρ) ∙ ⟦ suc n ∷ ys ⟧-Normal (i ∷ ρ) ∎
  ∙-NF-correct (suc n ∷ xs) (y ∷ ys) (i ∷ ρ) = begin
      i ∙ ⟦ ∙-NF (n ∷ xs) (y ∷ ys) ⟧-Normal (i ∷ ρ) ≈⟨ ∙-cong refl (∙-NF-correct (n ∷ xs) (y ∷ ys) (i ∷ ρ)) ⟩
      i ∙ (⟦ n ∷ xs ⟧-Normal (i ∷ ρ) ∙ ⟦ y ∷ ys ⟧-Normal (i ∷ ρ)) ≈⟨ sym (assoc _ _ _) ⟩
      ⟦ suc n ∷ xs ⟧-Normal (i ∷ ρ) ∙ ⟦ y ∷ ys ⟧-Normal (i ∷ ρ)   ∎

  ⟦_⇓⟧ : {n : ℕ} → Expr n → Env n → Carrier
  ⟦ x ⇓⟧ = ⟦ normalize x ⟧-Normal

  zeros-ε : {n : ℕ} (ρ : Env n) → ⟦ :0 ⇓⟧ ρ ≈ ⟦ :0 ⟧ ρ
  zeros-ε []      = refl
  zeros-ε (_ ∷ ρ) = zeros-ε ρ

  correct-var : {n : ℕ} (x : Fin n) (ρ : Env n) → ⟦ var x ⇓⟧ ρ ≈ ⟦ var x ⟧ ρ
  correct-var (suc i) (_ ∷ ρ) = correct-var i ρ
  correct-var zero    (x ∷ ρ) = begin
    x ∙ ⟦ replicate 0 ⟧-Normal ρ ≈⟨ ∙-cong refl (zeros-ε ρ) ⟩
    x ∙ ε                        ≈⟨ proj₂ identity x ⟩
    x                           ∎

  correct : {n : ℕ} (e : Expr n) (ρ : Env n) → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
  correct (var x)   ρ = correct-var x ρ
  correct :0        ρ = zeros-ε ρ
  correct (x₁ ⊕ x₂) ρ = begin
     ⟦ x₁ ⊕ x₂      ⇓⟧ ρ ≈⟨ ∙-NF-correct (normalize x₁) (normalize x₂) ρ ⟩
     ⟦ x₁ ⇓⟧ ρ ∙ ⟦ x₂ ⇓⟧ ρ ≈⟨ ∙-cong (correct x₁ ρ) (correct x₂ ρ) ⟩
     ⟦ x₁  ⟧ ρ ∙ ⟦ x₂  ⟧ ρ ∎

import Relation.Binary.Reflection as R
open R setoid var ⟦_⟧ ⟦_⇓⟧ correct public

private
  -- Now for a simple example
  Example = ∀ a b c d → (a ∙ ε ∙ b) ∙ (ε ∙ c ∙ d) ≈ a ∙ (b ∙ d) ∙ c

  -- A manual proof using equational reasoning looks like this.
  manual : Example
  manual a b c d = begin
    (a ∙  ε ∙ b)  ∙ (ε ∙  c  ∙ d)  ≈⟨ ∙-cong (assoc a ε b) (assoc ε c d) ⟩
    (a ∙ (ε ∙ b)) ∙ (ε ∙ (c  ∙ d)) ≈⟨ ∙-cong (∙-cong refl (idˡ b)) (idˡ (c ∙ d)) ⟩
    (a ∙      b)  ∙      (c  ∙ d)  ≈⟨ sym (assoc (a ∙ b) c d) ⟩
     a ∙      b   ∙       c  ∙ d   ≈⟨ assoc (a ∙ b) c d ⟩
    (a ∙      b)  ∙      (c  ∙ d)  ≈⟨ ∙-cong refl (comm c d) ⟩
    (a ∙      b)  ∙      (d  ∙ c)  ≈⟨ sym (assoc (a ∙ b) d c) ⟩
     a ∙      b   ∙       d  ∙ c   ≈⟨ ∙-cong (assoc a b d) refl ⟩
     a ∙     (b   ∙       d) ∙ c   ∎
    where
      open import Data.Product using (proj₁)
      idˡ = proj₁ identity

  -- Let's see the solver in action!
  automatic : Example
  automatic = solve 4 (λ a b c d → (a ⊕ :0 ⊕ b) ⊕ (:0 ⊕ c ⊕ d) ⊜ a ⊕ (b ⊕ d) ⊕ c) refl
                                -- ^ Here we reflect the shape of the proof we want
