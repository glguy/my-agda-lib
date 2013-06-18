------------------------------------------------------------------------
-- This module automates the process of producing equivalence proofs
-- on arbitrary Monoids using the Reflection module provided in Agda's
-- standard library.
--
-- Proofs involving associativity can be frustratingly mechanical, but this
-- module primarily serves as an introduction to the Reflection module.
--
-- For a more advanced use of the Reflection module, see Algebra.RingSolver
-- I have also implemented a Solver module for CommutativeMonoids.
--
-- What is a monoid?
-- A "Carrier" set of values
-- An equivalence _≈_
-- An associative, binary operation _∙_ which respects _≈_
-- An identity element ε
--
-- By the end of this module, we'll be able to automate proofs like:
-- ∀ a b c d → (a ∙ b) ∙ (c ∙ d) ≈ a ∙ (b ∙ c) ∙ d
------------------------------------------------------------------------

open import Algebra using (Group; module Group)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Fin.Props using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Vec using (Vec; lookup)
open import Data.List using (List; _∷_; []; [_]; _++_; foldr; _∷ʳ_; map; reverse)
open import Data.List.Properties
open import Data.Product using (proj₁; proj₂)
open import Level using (Level)
open import Data.Bool using (_xor_; true;false; Bool; not; if_then_else_)
open import Function using (_⟨_⟩_; _∘_)

module Algebra.GroupSolver {a ℓ : Level} (G : Group a ℓ) where

open Group G using (monoid; Carrier; _∙_; _≈_; ε; ∙-cong; assoc; identity; refl; setoid; sym; _⁻¹; inverse; ⁻¹-cong)
open import Relation.Binary.EqReasoning setoid using (begin_; _≈⟨_⟩_; _≡⟨_⟩_; _∎)
open import Algebra.Props.Group G
open import Algebra.Group.MoreProps G

-- The Syntax type allows us to reflect the shape of the proof
-- we wish to automate. We will "reflect" our goal into a Syntax
-- value and use this convert our proof obligation to a much
-- simpler one on normal forms. The 'n' is the number of unique
-- variables in the expression.

data Syntax (n : ℕ) : Set where
  _⊙_ : Syntax n → Syntax n → Syntax n
  var : Fin n → Syntax n
  :0 : Syntax n
  inv : Syntax n → Syntax n

infixl 7 _⊙_

-- This semantic evaluation function constructs a value
-- of Carrier which preserves the shape of the Syntax
-- tree. This is the shape of the proof we want to have.

⟦_⟧ : {n : ℕ} → Syntax n → Vec Carrier n → Carrier
⟦ x₁ ⊙ x₂ ⟧ ρ = ⟦ x₁ ⟧ ρ ∙ ⟦ x₂ ⟧ ρ
⟦ var i   ⟧ ρ = lookup i ρ
⟦ :0      ⟧ _ = ε
⟦ inv x   ⟧ ρ = ⟦ x ⟧ ρ ⁻¹

private
  record Term n : Set where
    constructor term
    field
      polarity : Bool
      index    : Fin n
  open Term

  not-term : {n : ℕ} → Term n → Term n
  not-term (term p i) = term (not p) i

  flatten : {n : ℕ} → Syntax n → List (Term n)
  flatten (x₁ ⊙ x₂) = flatten x₁ ++ flatten x₂
  flatten (var i)   = [ term true i ]
  flatten :0        = []
  flatten (inv x)   = map not-term (reverse (flatten x))

  resolve : {n : ℕ} → List (Term n) → Vec Carrier n → Carrier
  resolve [] ρ = ε
  resolve (term p index ∷ xs) ρ = (if p then lookup index ρ else lookup index ρ ⁻¹) ∙ resolve xs ρ

  resolve-++-comm : {n : ℕ} (x₁ x₂ : List (Term n)) (ρ : Vec Carrier n) →
      resolve (x₁ ++ x₂) ρ ≈ resolve x₁ ρ ∙ resolve x₂ ρ
  resolve-++-comm [] x₂ ρ = sym (proj₁ identity _)
  resolve-++-comm (term p i ∷ x₁) x₂ ρ = begin
      (if p then lookup i ρ else lookup i ρ ⁻¹) ∙ resolve (x₁ ++ x₂) ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ resolve-++-comm x₁ x₂ ρ ⟩ 
      (if p then lookup i ρ else lookup i ρ ⁻¹) ∙ (resolve x₁ ρ ∙ resolve x₂ ρ)
      ≈⟨ sym (assoc _ _ _) ⟩
      (if p then lookup i ρ else lookup i ρ ⁻¹) ∙ resolve x₁ ρ ∙ resolve x₂ ρ
    ∎

  simplify1 : {n : ℕ} → Term n → List (Term n) → List (Term n)
  simplify1 x [] = [ x ]
  simplify1 (term p₁ i₁) (term p₂ i₂ ∷ ys)  with p₁ xor p₂ | i₁ ≟ i₂
  ... | true | yes _ = ys
  ... | _    | _     = term p₁ i₁ ∷ term p₂ i₂ ∷ ys

  simplify : {n : ℕ} → List (Term n) → List (Term n)
  simplify = foldr simplify1 []

  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_) renaming ([_] to ≡[_])

  simplify1-preserves : {n : ℕ} (x : Term n) (xs : List (Term n)) (ρ : Vec Carrier n) →
      resolve (simplify1 x xs) ρ ≈ resolve (x ∷ xs) ρ
  simplify1-preserves x [] ρ = refl
  simplify1-preserves (term p₁ i₁) (term p₂ i₂ ∷ ys) ρ  with i₁ ≟ i₂
  simplify1-preserves (term true i₁) (term true i₂ ∷ ys) ρ | j = refl
  simplify1-preserves (term true i₁) (term false i₂ ∷ ys) ρ  | no ¬p = refl
  simplify1-preserves (term false i₁) (term true i₂ ∷ ys) ρ | no ¬p = refl
  simplify1-preserves (term false i₁) (term false i₂ ∷ ys) ρ | j = refl
  simplify1-preserves (term true i₁) (term false .(i₁) ∷ ys) ρ | yes ≡.refl = begin
    resolve ys ρ ≈⟨ sym (proj₁ identity _) ⟩
    ε ∙ resolve ys ρ ≈⟨ sym (proj₂ inverse _) ⟨ ∙-cong ⟩ refl ⟩ 
    lookup i₁ ρ ∙ lookup i₁ ρ ⁻¹ ∙ resolve ys ρ ≈⟨ assoc _ _ _ ⟩
    lookup i₁ ρ ∙ (lookup i₁ ρ ⁻¹ ∙ resolve ys ρ) ∎
  simplify1-preserves (term false i₁) (term true .(i₁) ∷ ys) ρ | yes ≡.refl = begin
    resolve ys ρ ≈⟨ sym (proj₁ identity _) ⟩
    ε ∙ resolve ys ρ ≈⟨ sym (proj₁ inverse _) ⟨ ∙-cong ⟩ refl ⟩ 
    lookup i₁ ρ ⁻¹ ∙ lookup i₁ ρ ∙ resolve ys ρ ≈⟨ assoc _ _ _ ⟩
    lookup i₁ ρ ⁻¹ ∙ (lookup i₁ ρ ∙ resolve ys ρ) ∎

  simplify-preserves : {n : ℕ} (x : List (Term n)) (ρ : Vec Carrier n) →
      resolve (simplify x) ρ ≈ resolve x ρ
  simplify-preserves [] ρ = refl
  simplify-preserves (x ∷ xs) ρ = begin
    resolve (simplify (x ∷ xs)) ρ ≈⟨ simplify1-preserves x (simplify xs) ρ ⟩
    (if polarity x then lookup (index x) ρ else lookup (index x) ρ ⁻¹) ∙ resolve (simplify xs) ρ ≈⟨ refl ⟨ ∙-cong ⟩ simplify-preserves xs ρ ⟩
    resolve (x ∷ xs) ρ ∎

-- This normalized semantic evaluation function constructs a
-- value of Carrier which is semantically equivalent to the
-- one produced by ⟦_⟧, however all occurences of _∙_ are
-- made right-associative and all ε elements are eliminated.
-- This is the shape of the proof we want to provide.

⟦_⇓⟧ : {n : ℕ} → Syntax n → Vec Carrier n → Carrier
⟦ x ⇓⟧ = resolve (simplify (flatten x))

private

  rev-inv : {n : ℕ} (x : Term n) (ρ : Vec Carrier n) → resolve [ not-term x ] ρ ≈ resolve [ x ] ρ ⁻¹
  rev-inv (term true index) ρ = begin
     lookup index ρ ⁻¹ ∙ ε ≈⟨ proj₂ identity _ ⟩
     lookup index ρ ⁻¹ ≈⟨ ⁻¹-cong (sym (proj₂ identity _)) ⟩
     (lookup index ρ ∙ ε) ⁻¹ ∎
  rev-inv (term false index) ρ = begin
     lookup index ρ ∙ ε ≈⟨ proj₂ identity _ ⟩
     lookup index ρ ≈⟨ sym (proj₁ identity _) ⟩
     ε ∙ lookup index ρ ≈⟨ sym inverse-unit ⟨ ∙-cong ⟩ sym (⁻¹-involutive _) ⟩
     ε ⁻¹ ∙ lookup index ρ ⁻¹ ⁻¹ ≈⟨ sym (⁻¹-∙-comm (lookup index ρ ⁻¹) ε) ⟩
     (lookup index ρ ⁻¹ ∙ ε) ⁻¹ ∎

  reverse-flatten1 : {n : ℕ} (xs : List (Term n)) (ρ : Vec Carrier n) →
        resolve (map not-term (reverse xs)) ρ ≈ resolve xs ρ ⁻¹
  reverse-flatten1 [] ρ = sym inverse-unit
  reverse-flatten1 (x ∷ xs) ρ = begin
    resolve (map not-term (reverse (x ∷ xs))) ρ ≡⟨ ≡.cong₂ resolve (≡.cong (map not-term) (reverse-++-commute [ x ] xs)) ≡.refl ⟩
    resolve (map not-term (reverse xs ++ [ x ])) ρ ≡⟨ ≡.cong₂ resolve (map-++-commute not-term (reverse xs) [ x ]) ≡.refl ⟩
    resolve (map not-term (reverse xs) ++ map not-term (reverse [ x ])) ρ ≈⟨ resolve-++-comm (map not-term (reverse xs)) [ not-term x ] ρ ⟩
    resolve (map not-term (reverse xs)) ρ ∙ resolve [ not-term x ] ρ ≈⟨ reverse-flatten1 xs ρ ⟨ ∙-cong ⟩ rev-inv x ρ ⟩
    resolve xs ρ ⁻¹ ∙ resolve [ x ] ρ ⁻¹ ≈⟨ sym (⁻¹-∙-comm (resolve [ x ] ρ) (resolve xs ρ)) ⟩
    (resolve [ x ] ρ ∙ resolve xs ρ) ⁻¹ ≈⟨ sym (⁻¹-cong (resolve-++-comm [ x ] xs ρ)) ⟩
    resolve (x ∷ xs) ρ ⁻¹ ∎

-- By proving that these two semantic evaluation functions produce
-- semantically equivalent values we'll be able to use equivalence
-- proofs about the normalized forms to talk about the equivalence
-- of the original values.

correct : {n : ℕ} (s : Syntax n) (ρ : Vec Carrier n) → ⟦ s ⇓⟧ ρ ≈ ⟦ s ⟧ ρ
correct :0        ρ = refl
correct (var i)   ρ = proj₂ identity _
correct (x₁ ⊙ x₂) ρ = begin
   ⟦ x₁      ⊙  x₂ ⇓⟧ ρ ≈⟨ simplify-preserves (flatten x₁ ++ flatten x₂) ρ ⟩
   resolve (flatten x₁ ++ flatten x₂) ρ ≈⟨ resolve-++-comm (flatten x₁) (flatten x₂) ρ ⟩
   resolve (flatten x₁) ρ ∙ resolve (flatten x₂) ρ ≈⟨ sym (simplify-preserves (flatten x₁) ρ ⟨ ∙-cong ⟩ simplify-preserves (flatten x₂) ρ) ⟩
   ⟦ x₁ ⇓⟧ ρ ∙ ⟦ x₂ ⇓⟧ ρ ≈⟨ ∙-cong (correct x₁ ρ) (correct x₂ ρ) ⟩
   ⟦ x₁  ⟧ ρ ∙ ⟦ x₂  ⟧ ρ ∎ 
correct (inv x) ρ = begin
  ⟦ inv x ⇓⟧ ρ ≈⟨ simplify-preserves (map not-term (reverse (flatten x))) ρ ⟩
  resolve (map not-term (reverse (flatten x))) ρ ≈⟨ reverse-flatten1 (flatten x) ρ ⟩
  resolve (flatten x) ρ ⁻¹ ≈⟨ ⁻¹-cong (sym (simplify-preserves (flatten x) ρ)) ⟩
  ⟦ x ⇓⟧ ρ ⁻¹ ≈⟨ ⁻¹-cong (correct x ρ) ⟩
  ⟦ inv x ⟧ ρ ∎

open import Relation.Binary.Reflection setoid var ⟦_⟧ ⟦_⇓⟧ correct public using (prove; close; solve; solve₁; _⊜_)
