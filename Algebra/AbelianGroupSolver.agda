open import Algebra using (module AbelianGroup; AbelianGroup; module CommutativeRing)

module Algebra.AbelianGroupSolver {a ℓ} (C : AbelianGroup a ℓ) where

open AbelianGroup C

open import Data.Fin     using (Fin; suc; zero)
open import Data.Vec     using (Vec; _∷_; []; lookup; replicate; zipWith; map)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_]; -_)
open import Data.Nat as ℕ    using (ℕ; _+_; suc; zero)
open import Data.Product using (proj₁; proj₂)
import Relation.Binary.EqReasoning as EqR
open EqR setoid
import Algebra.Group.Exponentiation as Exp
open Exp group
open import Function
import Algebra.CommutativeMonoidSolver as CMS
import Algebra.Props.Group as G
open G group
import Algebra.Props.AbelianGroup as AG
open AG C using (⁻¹-∙-comm)
data Expr (n : ℕ) : Set where
  _⊕_ : (x₁ x₂ : Expr n) → Expr n
  :0   : Expr n
  var  : (x : Fin n) → Expr n
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

  normalize : {n : ℕ} → Expr n → Normal n
  normalize (x₁ ⊕ x₂) = ∙-NF (normalize x₁) (normalize x₂)
  normalize (var x)   = var-NF x
  normalize :0        = replicate (+ 0)
  normalize (inv x)   = inv-NF (normalize x)
  
  ⟦_⟧-Normal : {n : ℕ} → Normal n → Env n → Carrier
  ⟦_⟧-Normal []           _       = ε
  ⟦_⟧-Normal (n ∷ ns) (x ∷ ρ) = x ^ n ∙ ⟦ ns ⟧-Normal ρ


  ∙-NF-correct : {n : ℕ} (x₁ x₂ : Normal n) (ρ : Env n) →
               ⟦ ∙-NF x₁ x₂ ⟧-Normal ρ ≈ ⟦ x₁ ⟧-Normal ρ ∙ ⟦ x₂ ⟧-Normal ρ
  ∙-NF-correct [] [] _ = sym (proj₂ identity ε)
  ∙-NF-correct (x ∷ xs) (y ∷ ys) (v ∷ ρ) = begin
     v ^ (x ℤ.+ y) ∙ ⟦ ∙-NF xs ys ⟧-Normal ρ ≈⟨ sym (exp-plus v x y) ⟨ ∙-cong ⟩ ∙-NF-correct xs ys ρ ⟩
     (v ^ x ∙ v ^ y) ∙ (⟦ xs ⟧-Normal ρ ∙ ⟦ ys ⟧-Normal ρ)
           ≈⟨ (let open CMS commutativeMonoid renaming (_⊕_ to _⊙_)
               in solve 4 (λ a₁ b c d → (a₁ ⊙ b) ⊙ (c ⊙ d) ⊜ (a₁ ⊙ c) ⊙ (b ⊙ d)) refl (v ^ x) (v ^ y) _ _) ⟩
     (v ^ x ∙ ⟦ xs ⟧-Normal ρ) ∙ (v ^ y ∙ ⟦ ys ⟧-Normal ρ) ∎

  ⟦_⇓⟧ : {n : ℕ} → Expr n → Env n → Carrier
  ⟦ x ⇓⟧ = ⟦ normalize x ⟧-Normal
  
  zeros-ε : {n : ℕ} (ρ : Env n) → ⟦ replicate (+ 0) ⟧-Normal ρ ≈ ε
  zeros-ε []      = refl
  zeros-ε (_ ∷ ρ) = trans (proj₁ identity _) (zeros-ε ρ)
  
  correct-var : {n : ℕ} (x : Fin n) (ρ : Env n) → ⟦ var x ⇓⟧ ρ ≈ ⟦ var x ⟧ ρ
  correct-var zero (x ∷ ρ) = begin
    (x ∙ ε) ∙ ⟦ replicate (+ 0) ⟧-Normal ρ ≈⟨ proj₂ identity x ⟨ ∙-cong ⟩ zeros-ε ρ ⟩
    x ∙ ε ≈⟨ proj₂ identity x ⟩
    x ∎
  correct-var (suc i) (x ∷ ρ) = begin
    ε ∙ ⟦ var i ⇓⟧ ρ ≈⟨ proj₁ identity _ ⟩
    ⟦ var i ⇓⟧ ρ ≈⟨ correct-var i ρ ⟩
    lookup i ρ ∎

  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  map-lift-involutive : ∀ {A : Set} {n : ℕ} (f : A → A) (x : Vec A n) →
                         (∀ x → f (f x) ≡ x) →
                          map f (map f x) ≡ x
  map-lift-involutive f [] invol = ≡.refl
  map-lift-involutive f (x ∷ x₁) invol = ≡.cong₂ _∷_ (invol x) (map-lift-involutive f x₁ invol)

  negation-involutive : (x : ℤ) → - (- x) ≡ x
  negation-involutive -[1+ n ] = ≡.refl
  negation-involutive (+ zero) = ≡.refl
  negation-involutive (+ suc n) = ≡.refl

  inverse-unit : ε ≈ ε ⁻¹
  inverse-unit = begin
     ε ≈⟨ sym (proj₂ inverse ε) ⟩
     (ε ∙ ε ⁻¹) ≈⟨ proj₁ identity _ ⟩
     ε ⁻¹ ∎

  invNF-∙-NF-comm : {n : ℕ} (x y : Vec ℤ n) → inv-NF (∙-NF x y) ≡ ∙-NF (inv-NF x) (inv-NF y)
  invNF-∙-NF-comm [] [] = ≡.refl
  invNF-∙-NF-comm (x ∷ x₁) (x₂ ∷ y) = ≡.cong₂ _∷_ (≡.sym (f x x₂)) (invNF-∙-NF-comm x₁ y)
    where
    import Data.Integer.Properties as P
    open AG (CommutativeRing.+-abelianGroup P.commutativeRing) renaming (⁻¹-∙-comm to f)
 
  negate-zeros : (n : ℕ) → inv-NF (replicate {n = n} (+ 0)) ≡ replicate (+ 0)
  negate-zeros zero = ≡.refl
  negate-zeros (suc n) = ≡.cong₂ _∷_ ≡.refl (negate-zeros n)

  correct-inv : {n : ℕ} (x : Expr n) (ρ : Env n) → ⟦ inv x ⇓⟧ ρ ≈ ⟦ inv x ⟧ ρ
  correct : {n : ℕ} (e : Expr n) (ρ : Env n) → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ

  correct-inv (x ⊕ x₁) ρ = begin
    ⟦ inv-NF (∙-NF (normalize x) (normalize x₁)) ⟧-Normal ρ ≡⟨ invNF-∙-NF-comm (normalize x) (normalize x₁) ⟨ ≡.cong₂ ⟦_⟧-Normal ⟩ ≡.refl ⟩
    ⟦ ∙-NF (inv-NF (normalize x)) (inv-NF (normalize x₁)) ⟧-Normal ρ ≈⟨ ∙-NF-correct (inv-NF (normalize x)) _ _ ⟩
    ⟦ inv-NF (normalize x) ⟧-Normal ρ ∙ ⟦ inv-NF (normalize x₁) ⟧-Normal ρ ≈⟨ correct-inv x ρ ⟨ ∙-cong ⟩ correct-inv x₁ ρ ⟩
    ⟦ x ⟧ ρ ⁻¹ ∙ ⟦ x₁ ⟧ ρ ⁻¹ ≈⟨ ⁻¹-∙-comm (⟦ x ⟧ ρ) (⟦ x₁ ⟧ ρ) ⟩
    (⟦ x ⟧ ρ ∙ ⟦ x₁ ⟧ ρ) ⁻¹ ∎
  correct-inv :0 [] = inverse-unit
  correct-inv :0 (x ∷ ρ) = trans (proj₁ identity _) (correct-inv :0 ρ)
  correct-inv {suc n} (var zero) (x ∷ ρ) = begin
    (x ⁻¹ ∙ ε) ∙ ⟦ inv-NF (replicate (+ 0)) ⟧-Normal ρ ≡⟨ ≡.refl ⟨ ≡.cong₂ _∙_ ⟩ (negate-zeros n ⟨ ≡.cong₂ ⟦_⟧-Normal ⟩ ≡.refl) ⟩
    (x ⁻¹ ∙ ε) ∙ ⟦ replicate (+ 0) ⟧-Normal ρ ≈⟨ proj₂ identity _ ⟨ ∙-cong ⟩ zeros-ε ρ ⟩
    x ⁻¹ ∙ ε ≈⟨ proj₂ identity _ ⟩
    x ⁻¹ ∎
  correct-inv (var (suc x)) (x₁ ∷ ρ) = trans (proj₁ identity _) (correct-inv (var x) ρ)
  correct-inv (inv x) ρ = begin
    ⟦ inv-NF (inv-NF (normalize x)) ⟧-Normal ρ
            ≡⟨ ≡.cong₂ ⟦_⟧-Normal (map-lift-involutive -_ (normalize x) negation-involutive) ≡.refl ⟩
    ⟦ normalize x ⟧-Normal ρ ≈⟨ correct x ρ ⟩
    ⟦ x ⟧ ρ ≈⟨ sym (⁻¹-involutive (⟦ x ⟧ ρ)) ⟩
    ⟦ x ⟧ ρ ⁻¹ ⁻¹ ∎
  
  correct (var x)   ρ = correct-var x ρ
  correct :0        ρ = zeros-ε ρ
  correct (x₁ ⊕ x₂) ρ = begin
     ⟦ x₁ ⊕ x₂      ⇓⟧ ρ ≈⟨ ∙-NF-correct (normalize x₁) (normalize x₂) ρ ⟩
     ⟦ x₁ ⇓⟧ ρ ∙ ⟦ x₂ ⇓⟧ ρ ≈⟨ ∙-cong (correct x₁ ρ) (correct x₂ ρ) ⟩
     ⟦ x₁  ⟧ ρ ∙ ⟦ x₂  ⟧ ρ ∎
  correct (inv x) ρ = correct-inv x ρ

import Relation.Binary.Reflection as R
open R setoid var ⟦_⟧ ⟦_⇓⟧ correct public
