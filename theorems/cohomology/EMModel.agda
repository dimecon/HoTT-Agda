{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import cohomology.Theory
open import cohomology.SpectrumModel
open import cohomology.WithCoefficients

module cohomology.EMModel where

module _ {i} (G : Group i) (G-abelian : is-abelian G) where

  open EMExplicit G G-abelian using (⊙EM; EM-level; EM-conn; spectrum)

  private
    E : (n : ℤ) → Ptd i
    E (pos m) = ⊙EM m
    E (negsucc m) = ⊙Lift ⊙Unit

    E-spectrum : (n : ℤ) → ⊙Ω (E (succ n)) == E n
    E-spectrum (pos n) = spectrum n
    E-spectrum (negsucc O) = ⊙ua $ ⊙≃-in
      (equiv (λ _ → _) (λ _ → idp)
             (λ _ → idp) (prop-has-all-paths (EM-level _ _ _) _))
      idp
    E-spectrum (negsucc (S n)) = ⊙ua $ ⊙≃-in
      (equiv (λ _ → _) (λ _ → idp)
             (λ _ → idp) (prop-has-all-paths (Lift-level Unit-is-set _ _) _))
      idp

  EM-Cohomology : CohomologyTheory i
  EM-Cohomology = spectrum-cohomology E E-spectrum

  open CohomologyTheory EM-Cohomology

  EM-dimension : (n : ℤ) → n ≠ 0 → C n (⊙Lift ⊙S⁰) == 0ᴳ
  EM-dimension (pos O) neq = ⊥-rec (neq idp)
  EM-dimension (pos (S n)) _ =
    contr-is-0ᴳ _ $ connected-at-level-is-contr
      (Trunc-level {n = 0})
      (Trunc-preserves-conn 0
        (transport (λ B → is-connected 0 B)
          (! (Bool⊙→-path _))
          (path-conn (connected-≤T (⟨⟩-monotone-≤ (≤-ap-S (O≤ n)))
                                   (EM-conn (S n))))))
  EM-dimension (negsucc O) _ =
    contr-is-0ᴳ _ $ Trunc-preserves-level 0 $ ⊙→-level $
      inhab-prop-is-contr idp (EM-level O _ _)
  EM-dimension (negsucc (S n)) _ =
    contr-is-0ᴳ _ $ Trunc-preserves-level 0 $ ⊙→-level $
      Lift-level Unit-is-prop _ _

  EM-Ordinary : OrdinaryTheory i
  EM-Ordinary = ordinary-theory EM-Cohomology EM-dimension
