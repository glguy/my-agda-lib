open import Algebra
open import Algebra.Structures
open import Relation.Binary
open import Function.Inverse
open import Level
open import Function.Equality
open import Data.Product

module Algebra.Group.InjectiveMapping {a ℓ}
   {A : Setoid a ℓ}
   where

Eq = A ⇨ A

isGroup : IsGroup (λ x y → Setoid._≈_ Eq (Inverse.from x) (Inverse.from y))
             Function.Inverse._∘_ Function.Inverse.id sym
isGroup = record { isMonoid = {!!}; inverse = (λ x x0 → {!Inverse.right-inverse-of (sym x) !}) , {!!}; ⁻¹-cong = {!!} }

S : Group (ℓ ⊔ a) (ℓ ⊔ a)
S = record {
      Carrier = Inverse A A;
      _≈_ = λ x y → Setoid._≈_ Eq (Inverse.from x) (Inverse.from y);
      _∙_ = Function.Inverse._∘_;
      ε = Function.Inverse.id;
      _⁻¹ = sym;
      isGroup = {!!} } -- Injection A A

