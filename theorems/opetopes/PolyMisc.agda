{-# OPTIONS --without-K #-}

open import HoTT

open import opetopes.Polynomial
open import opetopes.CartesianMorphism

module opetopes.PolyMisc where

  -- Unicity isos
  ⊚-unit-l : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → P ⇝ IdP I ⊚ P
  γ-map (⊚-unit-l P) c = c , (λ x → lift tt)
  ρ-eqv (⊚-unit-l P) = {!Σ₁-Unit!} -- (Σ₂-Lift-Unit)⁻¹
  τ-coh (⊚-unit-l P) p = {!!} -- idp

  -- ⊚-unit-inv-l : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → IdP I ⊚ P ⇝ P
  -- γ-map (⊚-unit-inv-l P) (c , φ) = c
  -- ρ-eqv (⊚-unit-inv-l P) = Σ₂-Lift-Unit
  -- τ-coh (⊚-unit-inv-l P) p = idp

  -- ⊚-unit-r : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → P ⇝ P ⊚ IdP I
  -- γ-map (⊚-unit-r P) c = lt , cst c
  -- ρ-eqv (⊚-unit-r P) = (Σ₁-Lift-Unit)⁻¹
  -- τ-coh (⊚-unit-r P) p = idp

  -- ⊚-unit-inv-r : ∀ {ℓ} {I : Type ℓ} (P : Poly I I) → P ⊚ IdP I  ⇝ P
  -- γ-map (⊚-unit-inv-r P) (lift unit , φ) = φ lt
  -- ρ-eqv (⊚-unit-inv-r P) = Σ₁-Lift-Unit
  -- τ-coh (⊚-unit-inv-r P) p = idp

  -- -- Associativity of polynomial composition
  -- module _ {ℓ} {I J K L : Type ℓ} (P : Poly I J) (Q : Poly J K) (R : Poly K L) where

  --   ⊚-assoc-r : (P ⊚ Q) ⊚ R ⇝ P ⊚ (Q ⊚ R) 
  --   γ-map ⊚-assoc-r (c , φ) = (c , fst ∘ φ) , (λ { (p₀ , p₁) → snd (φ p₀) p₁ })
  --   ρ-eqv ⊚-assoc-r {c = c , φ} = (Σ-assoc)⁻¹
  --   τ-coh ⊚-assoc-r {c = c , φ} (p , (l₀ , l₁)) = idp

  --   ⊚-assoc-l : P ⊚ (Q ⊚ R) ⇝ (P ⊚ Q) ⊚ R 
  --   γ-map ⊚-assoc-l ((c , φ) , ψ) = (c , λ p → (φ p , λ q → ψ (p , q)))
  --   ρ-eqv ⊚-assoc-l {c = (c , φ) , ψ} = Σ-assoc
  --   τ-coh ⊚-assoc-l {c = (c , φ) , ψ} p = idp

  -- module _ {ℓ} {I J K : Type ℓ} (P : Poly I J) (Q R : Poly J K) where

  --   ⊚-dist-⊕ : P ⊚ (Q ⊕ R) ⇝ (P ⊚ Q) ⊕ (P ⊚ R)
  --   γ-map ⊚-dist-⊕ (inl cq , φ) = inl (cq , φ)
  --   γ-map ⊚-dist-⊕ (inr cr , φ) = inr (cr , φ)
  --   ρ-eqv ⊚-dist-⊕ {c = inl cq , φ} = ide _
  --   ρ-eqv ⊚-dist-⊕ {c = inr cr , φ} = ide _
  --   τ-coh ⊚-dist-⊕ {c = inl cq , φ} p = idp
  --   τ-coh ⊚-dist-⊕ {c = inr cr , φ} p = idp
