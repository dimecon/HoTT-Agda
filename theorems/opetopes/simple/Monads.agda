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
            (δ : (p : Pl M c) → Op M (Ty M p)) → 
            (ε : (p : Pl M c) → SlOp (δ p)) → 
            SlOp (μ M c δ)

    SlPl : {i : Frm M} → {c : Op M i} → (w : SlOp c) → Type₀
    SlPl (dot i) = ⊥
    SlPl (box c δ ε) = ⊤ ⊔ Σ (Pl M c) (λ p → SlPl (ε p))

    SlTy : {i : Frm M} → {c : Op M i} → {w : SlOp c} → SlPl w → SlFrm M
    SlTy {w = dot _} ()
    SlTy {w = box c δ ε} (inl _) = (_ , c)
    SlTy {w = box c δ ε} (inr (p , n)) = SlTy n

  
    SlGrft : {i : Frm M} → {c : Op M i} → (w : SlOp c) → 
             (δ : (p : Pl M c) → Op M (Ty M p)) → 
             (ε : (p : Pl M c) → SlOp (δ p)) → 
             SlOp (μ M c δ)
    SlGrft (dot i) δ ε = transport↓ SlOp (ηp-compat M i) (unit-r M i δ) (ε (ηp M i))
    SlGrft (box c δ ε) δ₁ ε₁ = 
      transport! SlOp (assoc M _ c δ δ₁) (box c _ IH)

      where IH : (p : Pl M c) → SlOp (μ M (δ p) (λ q → transport (Op M) (μp-compat M _ c δ p q) (δ₁ (μp M c δ p q))))
            IH p = SlGrft (ε p) 
                          (λ q → transport (Op M) (μp-compat M _ c δ p q) (δ₁ (μp M c δ p q)))
                          (λ q → transport↓ SlOp (μp-compat M _ c δ p q) (from-transp (Op M) _ idp) (ε₁ (μp M c δ p q)))

  {-# TERMINATING #-}
  Slice : Monad → Monad
  Frm (Slice M) = SlFrm M
  Op (Slice M) (i , c) = SlOp M c
  Pl (Slice M) o = SlPl M o
  Ty (Slice M) p = SlTy M p
  η (Slice M) (i , c) = transport (SlOp M) (unit-l M i c) (box c (λ p → η M (Ty M p)) (λ p → dot (Ty M p))) 
  μ (Slice M) (dot i) δ = dot i
  μ (Slice M) (box c δ ε) κ = SlGrft M (κ (inl tt)) δ (λ p → μ (Slice M) (ε p) (λ q → κ (inr (p , q))))
  ηp (Slice M) i = ADMIT
  μp (Slice M) o δ p q = ADMIT
  ηp-unique (Slice M) i p = ADMIT
  ηp-compat (Slice M) i = ADMIT
  μp-compat (Slice M) i o δ p q = ADMIT
  unit-l (Slice M) i o = ADMIT
  unit-r (Slice M) i δ = ADMIT
  assoc (Slice M) i o δ δ₁ = ADMIT

  -- Right. Even though it's a bit of a mess, you seem to need the entire eliminator
  -- here, since the fibrations can vary with the place ...

  -- nodeTriv : (M : Monad) → 
  --            (P : {i : Frm M} → {c : Op M i} → {w : SlOp M (i , c)} → SlPl M w → Type₀) →
  --            (i : Frm M) → (p : SlPl M (dot i)) → P p
  -- nodeTriv M P i ()

  -- nodeElim : (M : Monad) → 
  --            (P : {i : Frm M} → {c : Op M i} → {w : SlOp M (i , c)} → SlPl M w → Type₀) →
  --            (x : (i : Frm M) → (c : Op M i) → 
  --                 (δ : (p : Pl M c) → Op M (Ty M p)) → 
  --                 (ε : (p : Pl M c) → SlOp M (Ty M p , δ p)) → P (this c δ ε)) → 
  --            (φ : (i : Frm M) → (c : Op M i) → 
  --                 (δ : (p : Pl M c) → Op M (Ty M p)) → 
  --                 (ε : (p : Pl M c) → SlOp M (Ty M p , δ p)) → 
  --                 (p : Pl M c) → (q : SlPl M (ε p)) → P (that c δ ε p q)) → 
  --            {i : Frm M} → {c : Op M i} → {w : SlOp M (i , c)} → (p : SlPl M w) → P p
  -- nodeElim M P x φ (this c δ ε) = x _ c δ ε
  -- nodeElim M P x φ (that c δ ε p q) = φ _ c δ ε p q

  -- consDot : (M : Monad) → (i : Frm M) → ⟦ Slice M ⟧⟦ dot i ≺ Op (Slice M) ⟧
  -- consDot M i ()

  -- consBox : (M : Monad) → {i : Frm M} → {c : Op M i} →
  --           {δ : (p : Pl M c) → Op M (Ty M p)} → 
  --           {ε : (p : Pl M c) → SlOp M (Ty M p , δ p)} → 
  --           (σ : SlOp M (i , c)) → 
  --           (φ : (p : Pl M c) → (q : Pl (Slice M) (ε p)) → SlOp M (Ty (Slice M) q)) → 
  --           (p : Pl (Slice M) (box c δ ε)) → SlOp M (Ty (Slice M) p)
  -- consBox M σ φ (this c δ ε) = σ
  -- consBox M σ φ (that c δ ε p q) = φ p q

  -- Id : Monad
  -- Frm Id = ⊤
  -- Op Id x = ⊤
  -- Pl Id o = ⊤
  -- Ty Id p = unit
  -- η Id i = unit
  -- μ Id o δ = unit
  -- ηp Id i = unit
  -- μp Id o δ p q = unit
  -- ηp-unique Id i p = idp
  -- ηp-compat Id i = idp
  -- μp-compat Id i o δ p q = idp
  -- unit-l Id i o = idp
  -- unit-r Id i δ = idp
  -- assoc Id i o δ δ₁ = idp
