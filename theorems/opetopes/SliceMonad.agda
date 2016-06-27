{-# OPTIONS --without-K #-}

open import HoTT

open import opetopes.Polynomial
open import opetopes.CartesianMorphism
open import opetopes.PolynomialMonad
open import opetopes.PolyMisc

module opetopes.SliceMonad where

  module _ {ℓ} {I : Type ℓ} (M : PolyMonad I) where

    open PolyMonad 

    data SlCons : (i : I) → γ (P M) i → Type ℓ where
      dot : (i : I) → SlCons i (⟪ η M ⟫ lt)
      box : (i : I) → (c : γ (P M) i) → 
            (δ : ⟦ P M ⟧⟦ c ≺ γ (P M) ⟧) → 
            (ε : (p : ρ (P M) c) → SlCons (τ (P M) p) (δ p)) → 
            SlCons i (⟪ μ M ⟫ (c , δ))

    data SlPl : (i : I) → (c : γ (P M) i) → SlCons i c → Type ℓ where
      here : (i : I) → (c : γ (P M) i) → 
             (δ : ⟦ P M ⟧⟦ c ≺ γ (P M) ⟧) → 
             (ε : (p : ρ (P M) c) → SlCons (τ (P M) p) (δ p)) → 
             SlPl i (⟪ μ M ⟫ (c , δ)) (box i c δ ε)
      there : (i : I) → (c : γ (P M) i) → 
              (δ : ⟦ P M ⟧⟦ c ≺ γ (P M) ⟧) → 
              (ε : (p : ρ (P M) c) → SlCons (τ (P M) p) (δ p)) → 
              (p : ρ (P M) c) → (q : SlPl (τ (P M) p) (δ p) (ε p)) → SlPl i (⟪ μ M ⟫ (c , δ)) (box i c δ ε)
      
    B : Type ℓ
    B = Σ I (γ (P M))

    {-# TERMINATING #-}
    SlP : Poly B B
    γ SlP (i , c) = SlCons i c
    ρ SlP {i , c} n = SlPl i c n
    τ SlP {.i , _} (here i c δ ε) = i , c
    τ SlP {.i , _} (there i c δ ε p q) = τ SlP q

    sl-η : IdP B ⇝ SlP
    γ-map sl-η {i , c} (lift unit) = {!box i c !}
    ρ-eqv sl-η = {!!}
    τ-coh sl-η p = {!!}

    -- γ-map sl-η {i , c} _ = (corolla c , γ≈ (η-left-law M c))
    -- ρ-eqv sl-η {i , c} = corolla-node-unique {P = P M} {c = c}
    -- τ-coh sl-η p = idp

    -- open ADMIT

    -- {-# TERMINATING #-}
    -- sl-join : {b : B} → γ (SlP ⊚ SlP) b → γ SlP b
    -- sl-join {i , ._} ((leaf .i , idp) , ψ) = ⟪ sl-η ⟫ lt
    -- sl-join {i , ._} ((node (c , φ) , idp) , ψ) = 
    --   (⟪ fr-μ (P M) ⟫ (localTree , fst ∘ IH) , ADMIT)  -- ! (γ≈ (ε-is-monad-map (localTree , fst ∘ IH))) ∙ {!!})

    --   where localCons : γ SlP (i , c)
    --         localCons = ψ (inl lt)

    --         localTree : W (P M) i
    --         localTree = fst localCons

    --         localEv : ⟪ ε ⟫ localTree == c
    --         localEv = snd localCons
  
    --         liftDec : ⟦ FrP (P M) ⟧⟦ localTree ≺ W (P M) ⟧
    --         liftDec = ⟪ ε ∣ W (P M) ↓ localEv ⟫⇑ φ

    --         nextTree : (l : leafOf localTree) → W (P M) (leafType l)
    --         nextTree l = liftDec l

    --         nextCons : (l : leafOf localTree) → γ (P M) (leafType l)
    --         nextCons l = ⟪ ε ⟫ (nextTree l)

    --         nodeCoe : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → nodeOf (node (c , φ))
    --         nodeCoe l n = inr (⟦ P M ↓ localEv ⟧↓ ( ⟪ ε ⟫↓ l) , nodeTrans (⟪ ε ∣ W (P M) ↓ localEv ⟫⇑-po φ l) n)

    --         nodeCoh : (l : leafOf localTree) → (n : nodeOf (nextTree l)) → nodeType n == nodeType (nodeCoe l n)
    --         nodeCoh l n = nodeTypeCoh (⟪ ε ∣ W (P M) ↓ localEv ⟫⇑-po φ l) n

    --         nextDec : (l : leafOf localTree) → ⟦ SlP ⟧⟦ nextTree l , idp ≺ γ SlP ⟧
    --         nextDec l n = transport (γ SlP)  (! (nodeCoh l n)) (ψ (nodeCoe l n)) 

    --         IH : (l : leafOf localTree) → γ SlP (leafType l , nextCons l)
    --         IH l = sl-join {leafType l , nextCons l} ((nextTree l , idp) , nextDec l)

    --         IH-ev : (l : leafOf localTree) → ⟪ ε ⟫ (fst (IH l)) == nextCons l
    --         IH-ev l = snd (IH l)

    --         -- unfold : ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) == 
    --         --          ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) 
    --         -- unfold = ⟪ μ M ⟫ (⟪ ε ⟫ localTree , (λ p → transport (γ (P M)) (⟪ ε ⓐ localTree ⟫↑= p) (⟪ ε ⟫ ((fst ∘ IH) (⟪ ε ⟫↑ p))))) =⟨ idp ⟩ 
    --         --          ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) ∎

    --         -- goal : ⟪ ε ⟫ (⟪ fr-μ (P M) ⟫ (localTree , fst ∘ IH)) == ⟪ ε ⟫ (node (c , φ))
    --         -- goal = ⟪ ε ⟫ (⟪ fr-μ (P M) ⟫ (localTree , fst ∘ IH)) =⟨ ! (γ≈ (ε-is-monad-map (localTree , fst ∘ IH))) ⟩
    --         --        ⟪ (ε ∥ ε) ▶ μ M ⟫ (localTree , fst ∘ IH) =⟨ {!ADMIT!} ⟩ 
                   
    --         --        ⟪ ε ⟫ (node (c , φ)) ∎

    -- sl-μ : SlP ⊚ SlP ⇝ SlP
    -- γ-map sl-μ = sl-join
    -- ρ-eqv sl-μ = ADMIT
    -- τ-coh sl-μ = ADMIT
   
    -- SlM : PolyMonad B
    -- P SlM = SlP
    -- η SlM = sl-η
    -- μ SlM = sl-μ
    -- η-left-law SlM c = ADMIT
    -- η-right-law SlM c = ADMIT
    -- μ-assoc-law SlM c = ADMIT

