{-# OPTIONS --without-K #-}

open import HoTT

module opetopes.simple.Monads where

  open ADMIT

  record Monad : Type₁ where
    field

      Frm : Type₀

      Op : Frm → Type₀
      Pl : {i : Frm} → (o : Op i) → Type₀
      Ty : {i : Frm} → {o : Op i} → (p : Pl o) → Frm

      η : (i : Frm) → Op i
      μ : {i : Frm} → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → Op i

      ηp : (i : Frm) → Pl (η i)
      μp : {i : Frm} → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → 
           (p : Pl o) → (q : Pl (δ p)) → Pl (μ o δ)

      ηp-unique : (i : Frm) → (p : Pl (η i)) → p == ηp i
      ηp-compat : (i : Frm) → Ty (ηp i) == i 
      μp-compat : (i : Frm) → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → 
                  (p : Pl o) → (q : Pl (δ p)) → Ty (μp o δ p q) == Ty q 

      unit-l : (i : Frm) → (o : Op i) → μ o (λ p → η (Ty p)) == o
      unit-r : (i : Frm) → (δ : (p : Pl (η i)) → Op (Ty p)) → 
               δ (ηp i) == μ (η i) δ [ Op ↓ ηp-compat i ]

      assoc : (i : Frm) → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → 
              (δ₁ : (q : Pl (μ o δ)) → Op (Ty q)) → 
              μ (μ o δ) δ₁ == μ o (λ p → μ (δ p) (λ q → transport Op (μp-compat i o δ p q) (δ₁ (μp o δ p q)))) 

  open Monad

  ⟦_⟧⟦_≺_⟧ : (M : Monad) → {i : Frm M} → (o : Op M i) → (X : Frm M → Type₀) → Type₀
  ⟦ M ⟧⟦ o ≺ X ⟧ = (p : Pl M o) → X (Ty M p)

  ⟦_⟧ : (M : Monad) → (X : Frm M → Type₀) → Frm M → Type₀
  ⟦ M ⟧ X i = Σ (Op M i) (λ o → ⟦ M ⟧⟦ o ≺ X ⟧)

  Id : Monad
  Frm Id = ⊤
  Op Id x = ⊤
  Pl Id o = ⊤
  Ty Id p = unit
  η Id i = unit
  μ Id o δ = unit
  ηp Id i = unit
  μp Id o δ p q = unit
  ηp-unique Id i p = idp
  ηp-compat Id i = idp
  μp-compat Id i o δ p q = idp
  unit-l Id i o = idp
  unit-r Id i δ = idp
  assoc Id i o δ δ₁ = idp

  SlFrm : Monad → Type₀
  SlFrm M = Σ (Frm M) (Op M)

  -- This must exist somewhere or somehow be definable ...
  transport↓ : {A : Type₀} {B : A → Type₀} (C : {a : A} → B a → Type₀) 
               {a₀ a₁ : A} {b₀ : B a₀} {b₁ : B a₁}
               (p : a₀ == a₁) (q : b₀ == b₁ [ B ↓ p ]) → 
               C b₀ → C b₁
  transport↓ C idp idp c = c

  module _ (M : Monad) where

    data SlOp : {i : Frm M} → (c : Op M i) → Type₀ where
      dot : (i : Frm M) → SlOp (η M i)
      box : {i : Frm M} → (c : Op M i) → 
            (ε : (p : Pl M c) → Σ (Op M (Ty M p)) SlOp) → 
            SlOp (μ M c (fst ∘ ε))

    SlPl : {i : Frm M} → {c : Op M i} → (w : SlOp c) → Type₀
    SlPl (dot i) = ⊥
    SlPl (box c ε) = ⊤ ⊔ Σ (Pl M c) (λ p → SlPl (snd (ε p)))

    SlTy : {i : Frm M} → {c : Op M i} → {w : SlOp c} → SlPl w → SlFrm M
    SlTy {w = dot _} ()
    SlTy {w = box c ε} (inl _) = (_ , c)
    SlTy {w = box c ε} (inr (p , n)) = SlTy n
  
    SlGrft : {i : Frm M} → {c : Op M i} → (w : SlOp c) → 
             (ε : (p : Pl M c) → Σ (Op M (Ty M p)) SlOp) → 
             SlOp (μ M c (fst ∘ ε))
    SlGrft (dot i) ε = transport↓ SlOp (ηp-compat M i) (unit-r M i (fst ∘ ε)) (snd (ε (ηp M i)))
    SlGrft (box c ε) ε₁ = transport! SlOp (assoc M _ c δ δ₁) (box c IH)

      where δ : (p : Pl M c) → Op M (Ty M p)
            δ = fst ∘ ε
  
            δ₁ : (p : Pl M (μ M c δ)) → Op M (Ty M p)
            δ₁ = fst ∘ ε₁

            α : (p : Pl M c) → (q : Pl M (δ p)) → Op M (Ty M q)
            α p q = transport (Op M) (μp-compat M _ c δ p q) (δ₁ (μp M c δ p q))

            β : (p : Pl M c) → (q : Pl M (δ p)) → SlOp (α p q)
            β p q = transport↓ SlOp (μp-compat M _ c δ p q) (from-transp (Op M) _ idp) (snd (ε₁ (μp M c δ p q)))

            IH : (p : Pl M c) → Σ (Op M (Ty M p)) SlOp
            IH p = μ M (δ p) (α p) , SlGrft (snd (ε p)) (λ q → α p q , β p q)

  {-# TERMINATING #-}
  Slice : Monad → Monad
  Frm (Slice M) = SlFrm M
  Op (Slice M) (i , c) = SlOp M c
  Pl (Slice M) o = SlPl M o
  Ty (Slice M) p = SlTy M p
  η (Slice M) (i , c) = transport (SlOp M) (unit-l M i c) (box c (λ p → η M (Ty M p) , dot (Ty M p)))
  μ (Slice M) (dot i) δ = dot i
  μ (Slice M) (box c ε) κ = SlGrft M (κ (inl tt)) (λ p → fst (ε p) , μ (Slice M) (snd (ε p)) (λ q → κ (inr (p , q))))
  ηp (Slice M) i = ADMIT
  μp (Slice M) o δ p q = ADMIT
  ηp-unique (Slice M) i p = ADMIT
  ηp-compat (Slice M) i = ADMIT
  μp-compat (Slice M) i o δ p q = ADMIT
  unit-l (Slice M) i o = ADMIT
  unit-r (Slice M) i δ = ADMIT
  assoc (Slice M) i o δ δ₁ = ADMIT

  nodeIn : (M : Monad) → 
           (P : {i : Frm M} → {c : Op M i} → (w : SlOp M c) → (p : SlPl M w) → Type₀) → 
           (φ : {i : Frm M} → (c : Op M i) → 
                (ε : (p : Pl M c) → Σ (Op M (Ty M p)) (SlOp M)) → 
                P (box c ε) (inl tt)) → 
           (ψ : {i : Frm M} → (c : Op M i) → 
                (ε : (p : Pl M c) → Σ (Op M (Ty M p)) (SlOp M)) → 
                (p : Pl M c) → (q : SlPl M (snd (ε p))) → P (box c ε) (inr (p , q))) → 
           {i : Frm M} → {c : Op M i} → {w : SlOp M c} → (p : SlPl M w) → P w p
  nodeIn M P φ ψ {w = dot _} ()
  nodeIn M P φ ψ {w = box c ε} (inl _) = φ c ε
  nodeIn M P φ ψ {w = box c ε} (inr (p , q)) = ψ c ε p q

  boxPair : (M : Monad) → {i : Frm M} → (c : Op M i) → Type₀
  boxPair M c = (p : Pl M c) → Σ (Op M (Ty M p)) (SlOp M)

  pairNil : (M : Monad) → (i : Frm M) → boxPair (Slice M) (dot i)
  pairNil M i ()

  nodeRec : (M : Monad) → {i : Frm M} → {c : Op M i} →
            (P : Frm (Slice M) → Type₀) → 
            {ε : (p : Pl M c) → Σ (Op M (Ty M p)) (SlOp M)} → 
            (x : P (i , c)) → 
            (φ : (p : Pl M c) → (q : SlPl M (snd (ε p))) → P (SlTy M q)) → 
            (p : SlPl M (box c ε)) → P (Ty (Slice M) p)
  nodeRec M P x φ (inl _) = x
  nodeRec M P x φ (inr (p , q)) = φ p q

  pairIntre : (M : Monad) → {i : Frm M} → {c : Op M i} →
              {ε : (p : Pl M c) → Σ (Op M (Ty M p)) (SlOp M)} → 
              (στ : Σ (SlOp M c) (SlOp (Slice M))) → 
              (κ : (p : Pl M c) → boxPair (Slice M) (snd (ε p))) → 
              boxPair (Slice M) (box c ε)
  pairIntre M {i} {c} στ κ p = nodeRec M (λ { (_ , d) → Σ (SlOp M d) (SlOp (Slice M)) }) στ κ p

  pairIntro : (M : Monad) → {i : Frm M} → {c : Op M i} →
              {ε : (p : Pl M c) → Σ (Op M (Ty M p)) (SlOp M)} → 
              (στ : Σ (SlOp M c) (SlOp (Slice M))) → 
              (κ : (p : Pl M c) → boxPair (Slice M) (snd (ε p))) → 
              boxPair (Slice M) (box c ε)
  pairIntro M στ κ (inl _) = στ
  pairIntro M στ κ (inr (p , q)) = κ p q
