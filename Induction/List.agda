open import Induction
open import Data.List
open import Data.Unit
open import Level

module Induction.List where

ListRec : {a : Level} (A : Set a) → RecStruct (List A)
ListRec A P [] = Lift ⊤
ListRec A P (_ ∷ xs) = P xs

list-rec-builder : {a : Level} (A : Set a) → RecursorBuilder (ListRec A)
list-rec-builder A P f [] = _
list-rec-builder A P f (x ∷ xs) = f xs (list-rec-builder A P f xs)

list-rec : {a : Level} (A : Set a) → Recursor (ListRec A)
list-rec A = build (list-rec-builder A)