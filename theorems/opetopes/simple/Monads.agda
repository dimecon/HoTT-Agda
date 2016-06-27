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
      μ : (i : Frm) → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → Op i

      ηp : (i : Frm) → Pl (η i)
      μp : (i : Frm) → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → 
           (p : Pl o) → (q : Pl (δ p)) → Pl (μ i o δ)

      ηp-unique : (i : Frm) → (p : Pl (η i)) → p == ηp i
      ηp-compat : (i : Frm) → Ty (ηp i) == i 
      μp-compat : (i : Frm) → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → 
                  (p : Pl o) → (q : Pl (δ p)) → Ty (μp i o δ p q) == Ty q 

      unit-l : (i : Frm) → (o : Op i) → μ i o (λ p → η (Ty p)) == o
      unit-r : (i : Frm) → (δ : (p : Pl (η i)) → Op (Ty p)) → 
               δ (ηp i) == μ i (η i) δ [ Op ↓ ηp-compat i ]

      assoc : (i : Frm) → (o : Op i) → (δ : (p : Pl o) → Op (Ty p)) → 
              (δ₁ : (q : Pl (μ i o δ)) → Op (Ty q)) → 
              μ i (μ i o δ) δ₁ == μ i o (λ p → μ (Ty p) (δ p) (λ q → transport Op (μp-compat i o δ p q) (δ₁ (μp i o δ p q)))) 

  open Monad

  ⟦_⟧⟦_≺_⟧ : (M : Monad) → {i : Frm M} → (o : Op M i) → (X : Frm M → Type₀) → Type₀
  ⟦ M ⟧⟦ o ≺ X ⟧ = (p : Pl M o) → X (Ty M p)

  ⟦_⟧ : (M : Monad) → (X : Frm M → Type₀) → Frm M → Type₀
  ⟦ M ⟧ X i = Σ (Op M i) (λ o → ⟦ M ⟧⟦ o ≺ X ⟧)

  SlFrm : Monad → Type₀
  SlFrm M = Σ (Frm M) (Op M)

  data SlOp (M : Monad) : SlFrm M → Type₀ where
    ext : (i : Frm M) → SlOp M (i , η M i)
    int : (i : Frm M) → (o : Op M i) → (δ : ⟦ M ⟧⟦ o ≺ Op M ⟧) →
          (ε : (p : Pl M o) → SlOp M (Ty M p , δ p)) → 
          SlOp M (i , μ M i o δ)

  data SlPl (M : Monad) : {b : SlFrm M} → SlOp M b → Type₀ where
    this : (i : Frm M) → (o : Op M i) → (δ : ⟦ M ⟧⟦ o ≺ Op M ⟧) →
           (ε : (p : Pl M o) → SlOp M (Ty M p , δ p)) → 
           SlPl M (int i o δ ε)
    that : (i : Frm M) → (o : Op M i) → (δ : ⟦ M ⟧⟦ o ≺ Op M ⟧) →
           (ε : (p : Pl M o) → SlOp M (Ty M p , δ p)) → 
           (p : Pl M o) → (q : SlPl M (ε p)) → SlPl M (int i o δ ε)

  SlTy : (M : Monad) {i : SlFrm M} {tr : SlOp M i} (n : SlPl M tr) → SlFrm M
  SlTy M (this i o δ ε) = i , o
  SlTy M (that i o δ ε p n) = SlTy M n

  SlGrft : (M : Monad) → (i : Frm M) → (o : Op M i) → 
           (tr : SlOp M (i , o)) → (δ : ⟦ M ⟧⟦ o ≺ Op M ⟧) →
           (ε : (p : Pl M o) → SlOp M (Ty M p , δ p)) → 
           SlOp M (i , μ M i o δ)
  SlGrft M i .(η M i) (ext .i) δ ε = transport (SlOp M) (pair= (ηp-compat M i) (unit-r M i δ)) (ε (ηp M i)) 
  SlGrft M i .(μ M i o δ) (int .i o δ ε) δ₁ ε₁ = 
    transport! (λ x → SlOp M (i , x)) (assoc M i o δ δ₁) 
      (int i o (λ p → (μ M (Ty M p) (δ p) (λ q → transport (Op M) (μp-compat M i o δ p q) (δ₁ (μp M i o δ p q))))) IH)

    where IH : (p : Pl M o) → SlOp M (Ty M p , μ M (Ty M p) (δ p) (λ q → transport (Op M) (μp-compat M i o δ p q) (δ₁ (μp M i o δ p q))))
          IH p =  SlGrft M (Ty M p) (δ p) (ε p) 
            (λ q → transport (Op M) (μp-compat M i o δ p q) (δ₁ (μp M i o δ p q))) 
            (λ q → transport (SlOp M) (pair= (μp-compat M i o δ p q) (from-transp (Op M) _ idp)) (ε₁ (μp M i o δ p q))) 


  {-# TERMINATING #-}
  Slice : Monad → Monad
  Frm (Slice M) = SlFrm M
  Op (Slice M) i = SlOp M i
  Pl (Slice M) o = SlPl M o
  Ty (Slice M) p = SlTy M p
  η (Slice M) (i , o) = transport (λ x → SlOp M (i , x)) (unit-l M i o) (int i o (λ p → η M (Ty M p)) (λ p → ext (Ty M p)))
  μ (Slice M) (i , .(η M i)) (ext .i) δ = ext i
  μ (Slice M) (i , .(μ M i o δ)) (int .i o δ ε) κ = 
    SlGrft M i o (κ (this i o δ ε)) δ (λ p → μ (Slice M) (Ty M p , δ p) (ε p) (λ q → κ (that i o δ ε p q)))
  ηp (Slice M) (i , o) = ADMIT
  ηp-unique (Slice M) i p = ADMIT
  ηp-compat (Slice M) i = ADMIT
  μp (Slice M) i o δ p q = ADMIT
  μp-compat (Slice M) i o δ p q = ADMIT
  unit-l (Slice M) i o = ADMIT
  unit-r (Slice M) i δ = ADMIT
  assoc (Slice M) i o δ δ₁ = ADMIT

  Id : Monad
  Frm Id = ⊤
  Op Id x = ⊤
  Pl Id o = ⊤
  Ty Id p = unit
  η Id i = unit
  μ Id i o δ = unit
  ηp Id i = unit
  μp Id i o δ p q = unit
  ηp-unique Id i p = idp
  ηp-compat Id i = idp
  μp-compat Id i o δ p q = idp
  unit-l Id i o = idp
  unit-r Id i δ = idp
  assoc Id i o δ δ₁ = idp
