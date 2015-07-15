module Data.Nat.Tactic where

open import Category.Monad using (module RawMonad)
open import Category.Monad.State using (StateMonad; State)
open import Data.Bool using (Bool; if_then_else_)
open import Data.List using (List; _∷_; []; [_]; _∷ʳ_; map; length; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using (module SemiringSolver)
open import Data.Product using (_,_; ,_; ∃; proj₁; proj₂)
open import Function using (case_of_; _∘_)
open import Reflection
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)

private
  Env = List Term
  open RawMonad (StateMonad Env)

  findIndex : ∀{a} {A : Set a} → (A → Bool) → List A → Maybe ℕ
  findIndex p = go 0
    where
    go : ℕ → List _ → Maybe ℕ
    go _ []       = nothing
    go i (x ∷ xs) = if p x then just i else go (suc i) xs


  mkArg : Term → Arg Term
  mkArg = arg (arg-info visible relevant)

  def′ : Name → List Term → Term
  def′ n xs = def n (Data.List.map mkArg xs)

  con′ : Name → List Term → Term
  con′ n xs = con n (Data.List.map mkArg xs)


  open SemiringSolver

  add : Term → Term → Term
  add x y = def′ (quote _:+_) (x ∷ y ∷ [])

  mult : Term → Term → Term
  mult x y = def′ (quote _:*_) (x ∷ y ∷ [])

  equals : Term → Term → Term
  equals x y = def′ (quote _:=_) (x ∷ y ∷ [])

  constant : ℕ → Term
  constant n = con′ (quote Polynomial.con) [ lit (nat n) ]

  abstraction : Term → State Env Term
  abstraction t env =
    case (findIndex (λ x → ⌊ x ≟ t ⌋) env) of λ
    { (just v′) → var v′           [] , env
    ; nothing   → var (length env) [] , env ∷ʳ t
    }

  arithExpr : Term → State Env Term
  arithExpr (lit (nat n))                              = return (constant n)
  arithExpr (con (quote suc) (arg _ n ∷ []))           = add (constant 1) <$> arithExpr n
  arithExpr (con (quote zero) [])                      = return (constant 0)
  arithExpr (def (quote _+_) (arg _ l ∷ arg _ r ∷ [])) = add  <$> arithExpr l ⊛ arithExpr r
  arithExpr (def (quote _*_) (arg _ l ∷ arg _ r ∷ [])) = mult <$> arithExpr l ⊛ arithExpr r
  arithExpr t                                          = abstraction t

  mkLams : Term → ℕ → Term
  mkLams t = fold t (lam visible ∘ abs "x")

autoSolve : List (Arg Type) → Term → Term
autoSolve _ (def (quote _≡_) (_ ∷ _ ∷ arg _ l ∷ arg _ r ∷ [])) = def′ (quote solve) args
  where
  termenv    = (equals <$> arithExpr l ⊛ arithExpr r) []
  term       = proj₁ termenv
  env        = proj₂ termenv

  envSize    = length env
  sizeArg    = lit (nat envSize)
  lambdaArg  = mkLams term envSize
  reflArg    = con (quote refl) []
  varArgs    = reverse env
  args       = sizeArg ∷ lambdaArg ∷ reflArg ∷ varArgs

autoSolve _ _ = unknown

private
  testCase : {x : ℕ} → x + 1 ≡ 1 + x
  testCase = tactic autoSolve

  testCase1 : {f : ℕ → ℕ}{x y : ℕ} → x * 3 + f y ≡ x + f y + x + x
  testCase1 = tactic autoSolve
