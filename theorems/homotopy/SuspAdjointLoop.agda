{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.PtdAdjoint

module homotopy.SuspAdjointLoop where

module Σ⊣Ω {i} where

  SuspFunctor : PtdFunctor i i
  SuspFunctor = record {
    obj = ⊙Susp;
    arr = ⊙susp-fmap;
    id = ⊙susp-fmap-idf;
    comp = ⊙susp-fmap-∘}

  LoopFunctor : PtdFunctor i i
  LoopFunctor = record {
    obj = ⊙Ω;
    arr = ⊙ap;
    id = λ _ → ⊙ap-idf;
    comp = ⊙ap-∘}

  module _ (X : Ptd i) where

    η : fst X → Ω (⊙Susp X)
    η x = merid x ∙ ! (merid (snd X))

    module E = SuspensionRec (snd X) (snd X) (idf _)

    ε : fst (⊙Susp (⊙Ω X)) → fst X
    ε = E.f

    ⊙η : fst (X ⊙→ ⊙Ω (⊙Susp X))
    ⊙η = (η , !-inv-r (merid (snd X)))

    ⊙ε : fst (⊙Susp (⊙Ω X) ⊙→ X)
    ⊙ε = (ε , idp)

  η-natural : {X Y : Ptd i} (f : fst (X ⊙→ Y))
    → ⊙η Y ⊙∘ f == ⊙ap (⊙susp-fmap f) ⊙∘ ⊙η X
  η-natural {X = X} (f , idp) = ⊙λ=
    (λ x → ! $
      ap-∙ (susp-fmap f) (merid x) (! (merid (snd X)))
      ∙ SuspFmap.merid-β f x
        ∙2 (ap-! (susp-fmap f) (merid (snd X))
            ∙ ap ! (SuspFmap.merid-β f (snd X))))
    (pt-lemma (susp-fmap f) (merid (snd X)) (SuspFmap.merid-β f (snd X)))
    where
    pt-lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} (p : x == y) {q : f x == f y} (α : ap f p == q)
      → !-inv-r q == (! $ ap-∙ f p (! p) ∙ α ∙2 (ap-! f p ∙ ap ! α))
                     ∙ ap (ap f) (!-inv-r p) ∙ idp
    pt-lemma f idp idp = idp

  ε-natural : {X Y : Ptd i} (f : fst (X ⊙→ Y))
    → ⊙ε Y ⊙∘ ⊙susp-fmap (⊙ap f) == f ⊙∘ ⊙ε X
  ε-natural (f , idp) = ⊙λ=
    (SuspensionElim.f idp idp
      (λ p → ↓-='-from-square $ vert-degen-square $
        ap-∘ (ε _) (susp-fmap (ap f)) (merid p)
        ∙ ap (ap (ε _)) (SuspFmap.merid-β (ap f) p)
        ∙ E.merid-β _ (ap f p)
        ∙ ap (ap f) (! (E.merid-β _ p))
        ∙ ∘-ap f (ε _) (merid p)))
    idp

  εΣ-Ση : (X : Ptd i) → ⊙ε (⊙Susp X) ⊙∘ ⊙susp-fmap (⊙η X) == ⊙idf _
  εΣ-Ση X = ⊙λ=
    (SuspensionElim.f
      idp
      (merid (snd X))
      (λ x → ↓-='-from-square $
        (ap-∘ (ε (⊙Susp X)) (susp-fmap (η X)) (merid x)
         ∙ ap (ap (ε (⊙Susp X))) (SuspFmap.merid-β (η X) x)
         ∙ E.merid-β _ (merid x ∙ ! (merid (snd X))))
        ∙v⊡ square-lemma (merid x) (merid (snd X))
        ⊡v∙ ! (ap-idf (merid x))))
    idp
    where
    square-lemma : ∀ {i} {A : Type i} {x y z : A}
      (p : x == y) (q : z == y)
      → Square idp (p ∙ ! q) p q
    square-lemma idp idp = ids

  Ωε-ηΩ : (X : Ptd i) → ⊙ap (⊙ε X) ⊙∘ ⊙η (⊙Ω X) == ⊙idf _
  Ωε-ηΩ X = ⊙λ=
    (λ p → ap-∙ (ε X) (merid p) (! (merid idp))
         ∙ (E.merid-β X p ∙2 (ap-! (ε X) (merid idp) ∙ ap ! (E.merid-β X idp)))
         ∙ ∙-unit-r _)
    (pt-lemma (ε X) (merid idp) (E.merid-β X idp))
    where
    pt-lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} (p : x == y) {q : f x == f y} (α : ap f p == q)
      → ap (ap f) (!-inv-r p) ∙ idp
        == (ap-∙ f p (! p) ∙ (α ∙2 (ap-! f p ∙ ap ! α)) ∙ !-inv-r q) ∙ idp
    pt-lemma f idp idp = idp

  adj : CounitUnitAdjoint SuspFunctor LoopFunctor
  adj = record {
    η = ⊙η;
    ε = ⊙ε;

    η-natural = η-natural;
    ε-natural = ε-natural;

    εF-Fη = εΣ-Ση;
    Gε-ηG = Ωε-ηΩ}

