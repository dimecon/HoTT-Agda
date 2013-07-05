{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Paths

module lib.types.Torus where

{-
data Torus : Type₀ where
  baseT : Torus
  loopT1 : baseT == baseT
  loopT2 : baseT == baseT
  surfT : loopT1 ∙ loopT2 == loopT2 ∙ loopT1
-}

module _ where
  private
    data #Torus : Type₀ where
      #baseT : #Torus

  Torus : Type₀
  Torus = #Torus

  baseT : Torus
  baseT = #baseT

  postulate  -- HIT
    loopT1 : baseT == baseT
    loopT2 : baseT == baseT
    surfT : loopT1 ∙ loopT2 == loopT2 ∙ loopT1

  {- Dependent elimination and computation rules -}
  module TorusElim {i} {A : Torus → Type i} (baseT* : A baseT)
    (loopT1* : baseT* == baseT* [ A ↓ loopT1 ])
    (loopT2* : baseT* == baseT* [ A ↓ loopT2 ])
    (surfT* : loopT1* ∙dep loopT2* == loopT2* ∙dep loopT1*
              [ (λ p → baseT* == baseT* [ A ↓ p ]) ↓ surfT ]) where

    f : Π Torus A
    f #baseT = baseT*

    postulate  -- HIT
      loopT1-β : apd f loopT1 == loopT1*
      loopT2-β : apd f loopT2 == loopT2*

    private
      lhs : apd f (loopT1 ∙ loopT2) == loopT1* ∙dep loopT2*
      lhs =
        apd f (loopT1 ∙ loopT2)                   =⟨ apd-∙ f loopT1 loopT2 ⟩
        apd f loopT1 ∙dep apd f loopT2            =⟨ loopT1-β |in-ctx (λ u → u ∙dep apd f loopT2) ⟩
        loopT1* ∙dep apd f loopT2                 =⟨ loopT2-β |in-ctx (λ u → loopT1* ∙dep u) ⟩
        loopT1* ∙dep loopT2* ∎

      rhs : apd f (loopT2 ∙ loopT1) == loopT2* ∙dep loopT1*
      rhs =
        apd f (loopT2 ∙ loopT1)                   =⟨ apd-∙ f loopT2 loopT1 ⟩
        apd f loopT2 ∙dep apd f loopT1            =⟨ loopT2-β |in-ctx (λ u → u ∙dep apd f loopT1) ⟩
        loopT2* ∙dep apd f loopT1                 =⟨ loopT1-β |in-ctx (λ u → loopT2* ∙dep u) ⟩
        loopT2* ∙dep loopT1* ∎

    postulate  -- HIT
      surfT-β : apd (apd f) surfT == lhs ◃ (surfT* ▹! rhs)

module TorusRec {i} {A : Type i} (baseT* : A) (loopT1* loopT2* : baseT* == baseT*)
  (surfT* : loopT1* ∙ loopT2* == loopT2* ∙ loopT1*) where

  private
    module M = TorusElim {A = λ _ → A} baseT* (↓-cst-in loopT1*) (↓-cst-in loopT2*)
                         (↓-cst-in-∙ loopT1 loopT2 loopT1* loopT2*
                         !◃ (↓-cst-in2 surfT* ▹ (↓-cst-in-∙ loopT2 loopT1 loopT2* loopT1*)))

  f : Torus → A
  f = M.f

  loopT1-β : ap f loopT1 == loopT1*
  loopT1-β = apd=cst-in M.loopT1-β

  loopT2-β : ap f loopT2 == loopT2*
  loopT2-β = apd=cst-in M.loopT2-β

  private
    lhs : ap f (loopT1 ∙ loopT2) == loopT1* ∙ loopT2*
    lhs =
      ap f (loopT1 ∙ loopT2)      =⟨ ap-∙ f loopT1 loopT2 ⟩
      ap f loopT1 ∙ ap f loopT2   =⟨ loopT1-β |in-ctx (λ u → u ∙ ap f loopT2) ⟩
      loopT1* ∙ ap f loopT2       =⟨ loopT2-β |in-ctx (λ u → loopT1* ∙ u) ⟩
      loopT1* ∙ loopT2* ∎

    rhs : ap f (loopT2 ∙ loopT1) == loopT2* ∙ loopT1*
    rhs =
      ap f (loopT2 ∙ loopT1)      =⟨ ap-∙ f loopT2 loopT1 ⟩
      ap f loopT2 ∙ ap f loopT1   =⟨ loopT2-β |in-ctx (λ u → u ∙ ap f loopT1) ⟩
      loopT2* ∙ ap f loopT1       =⟨ loopT1-β |in-ctx (λ u → loopT2* ∙ u) ⟩
      loopT2* ∙ loopT1* ∎

  postulate  -- Does not look easy
    surfT-β : ap (ap f) surfT == (lhs ∙ surfT*) ∙ (! rhs)
--  surfT-β = {!M.surfT-β!}

-- module TorusRecType {i} (baseT* : Type i) (loopT1* loopT2* : baseT* ≃ baseT*)
--   (surfT* : (x : baseT*) → –> loopT2* (–> loopT2* x) == –> loopT1* (–> loopT2* x)) where

--   open TorusRec baseT* (ua loopT1*) (ua loopT2*) {!!} public
--   -- TODO
