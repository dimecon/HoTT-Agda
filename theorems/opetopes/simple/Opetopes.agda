{-# OPTIONS --without-K #-}

open import HoTT
open import opetopes.simple.Monads

module opetopes.simple.Opetopes where

  open Monad

  --
  --  Unlabeled opetopes
  --

  OpMnd : ℕ → Monad
  OpMnd O = Id
  OpMnd (S n) = Slice (OpMnd n)

  Opetope : ℕ → Type₀
  Opetope n = Frm (OpMnd n)

  object : Opetope 0
  object = unit
  
  arrow : Opetope 1
  arrow = unit , unit

  drop : Opetope 2
  drop = (unit , unit) , dot unit

  glob : Opetope 2
  glob = (unit , unit) , (box unit (λ p → unit) (λ p → snd (drop)))

  simplex : Opetope 2
  simplex = (unit , unit) , (box unit (λ p → unit) (λ p → snd (glob)))

  --
  --  Opetopes is a general monad
  --

  NSlice : ℕ → Monad → Monad
  NSlice O M = M
  NSlice (S n) M = Slice (NSlice n M)

  MOp : ℕ → Monad → Type₀
  MOp n M = Frm (NSlice n M )

  mobj : (M : Monad) → (i : Frm M) → MOp 0 M
  mobj M i = i

  marrow : (M : Monad) → (i : Frm M) → (c : Op M i) → MOp 1 M
  marrow M i c = i , μ M c (λ p → η M (Ty M p)) -- And *this* is normal form!

  mdrop : (M : Monad) → (i : Frm M) → MOp 2 M
  mdrop M i = (i , η M i) , (dot i)

  mglob : (M : Monad) → (i : Frm M) → (c : Op M i) → MOp 2 M
  mglob M i c = (i , μ M c (λ p → η M (Ty M p))) , 
                box c (λ p → η M (Ty M p)) 
                      (λ p → dot (Ty M p))

  msimplex : (M : Monad) → (i : Frm M) → (c : Op M i) → (δ : (p : Pl M c) → Op M (Ty M p)) → MOp 2 M
  msimplex M i c δ = (i , (μ M c (λ p → μ M (δ p) (λ q → η M (Ty M q))))) , 
                      box c (λ p → μ M (δ p) (λ q → η M (Ty M q))) 
                            (λ p → box (δ p) (λ q → η M (Ty M q)) (λ q → dot (Ty M q)))


  -- globsimp : (M : Monad) → (i : Frm M) → (c : Op M i) → (δ : (p : Pl M c) → Op M (Ty M p)) → MOp 3 M
  -- globsimp M i c δ = (((i , (μ M c (λ p → μ M (δ p) (λ q → η M (Ty M q))))), γ),
  --                    box (box c (λ p → μ M (δ p) (λ q → η M (Ty M q))) (λ p → box (δ p) (λ q → η M (Ty M q)) (λ q → dot (Ty M q)))) 
  --                        (λ { (this .c .δ' _) → η (Slice M) (i , c) ; 
  --                             (that .c .δ' _ p (this .(δ p) _ _)) → η (Slice M) (Ty M p , δ p) ; 
  --                             (that .c .δ' _ p (that .(δ p) _ _ q ())) }) 
  --                        (λ { (this .c .δ' _) → dot (i , c) ; 
  --                             (that .c .δ' _ p (this .(δ p) _ _)) → dot (Ty M p , δ p) ; 
  --                             (that .c .δ' _ p (that .(δ p) _ _ q ())) })
  --                        )

  --        where δ' : (p : Pl M c) → Op M (Ty M p)
  --              δ' p = μ M (δ p) (λ q → η M (Ty M q))

  --              γ : SlOp M (i , μ M c δ')
  --              γ = μ (Slice M) (box c (λ p → μ M (δ p) (λ q → η M (Ty M q))) (λ p → box (δ p) (λ q → η M (Ty M q)) (λ q → dot (Ty M q))))
  --                  (λ { (this .c .δ' _) → η (Slice M) (i , c) ; 
  --                       (that .c .δ' _ p (this .(δ p) _ _)) → η (Slice M) (Ty M p , δ p) ; 
  --                       (that .c .δ' _ p (that .(δ p) _ _ q ())) })


  η↑ : (M : Monad) → {i : Frm M} → (c : Op M i) → Op M i
  η↑ M c = μ M c (λ p → η M (Ty M p))
  
  -- Right, so this version is pretty interesting, because everything in dimension
  -- higher than 1 is in fact expressed in terms of monad multiplications and eta
  -- expansions.  Does it seem like this could possibly continue?
  -- blobsimp : (M : Monad) → (i : Frm M) → (c : Op M i) → (δ : (p : Pl M c) → Op M (Ty M p)) → MOp 3 M
  -- blobsimp M i c δ = (((i , μ M c δ'), γ'), b')

  --        where δ' : (p : Pl M c) → Op M (Ty M p)
  --              δ' p = μ M (δ p) (λ q → η M (Ty M q))

  --              σ : SlOp M (i , μ M c δ')
  --              σ = box c δ' (λ p → box (δ p) (λ q → η M (Ty M q)) (λ q → dot (Ty M q)))

  --              γ' : SlOp M (i , μ M c δ')
  --              γ' = η↑ (Slice M) σ

  --              b' : SlOp (Slice M) ((i , μ M c δ'), γ')
  --              b' = η (Slice (Slice M)) ((i , μ M c δ') , γ')

  -- -- Okay, so the my new question is: what exactly does eta-expanded *mean* for the 
  -- -- case of γ above? I mean, this thing is just supposed to be a constructor, but it
  -- -- looks as though it's "normal form" is not given in terms of just constructor 
  -- -- applications, but rather by appeal to the multiplication.

  -- -- This would seem to imply that your normal forms will also have multiplications
  -- -- in higher dimensions, not merely constructor expressions.  Is this reasonable,
  -- -- or are you way off in the deep end at this point?

  -- -- I don't quite understand why there seems to be an index shift here, but since
  -- -- we can put an arbitrary multiplication in the top dimension, this seems more
  -- -- appropriate than simply adding a top dimensional η to give the cell .. hmm...

  eric : (M : Monad) → (i : Frm M) → (c : Op M i) → 
         (δ : (p : Pl M c) → Op M (Ty M p)) → 
         (ε : (p : Pl M (μ M c (λ p → η↑ M (δ p)))) → Op M (Ty M p)) → MOp 3 M
  eric M i c δ ε = ((i , μ M (μ M c δ') ε') , γ) , b

    where δ' : (p : Pl M c) → Op M (Ty M p)
          δ' p = η↑ M (δ p)

          ε' : (p : Pl M (μ M c δ')) → Op M (Ty M p)
          ε' p = η↑ M (ε p)

          σ : SlOp M (μ M c δ')
          σ = box c δ' (λ p → box (δ p) (λ q → η M (Ty M q)) (λ q → dot (Ty M q)))

          τ : SlOp M (μ M (μ M c δ') ε')
          τ = box (μ M c δ') ε' (λ p → box (ε p) (λ q → η M (Ty M q)) (λ q → dot (Ty M q)))

          γ : SlOp M (μ M (μ M c δ') ε')
          γ = μ (Slice M) τ (consBox M σ 
                            (λ p → consBox M (η (Slice M) (Ty M p , ε p)) 
                            (λ q → consDot M (Ty M q))))
                             
          b : SlOp (Slice M) γ
          b = box τ φ ψ
  
                  where pr : boxPair (Slice M) τ
                        pr = pairIntro M σ (η (Slice (Slice M)) ((i , μ M c δ') , σ)) 
                             (λ p → pairIntro M (η (Slice M) (Ty M p , ε p)) (η (Slice (Slice M)) ((Ty M p , ε p) , η (Slice M) (Ty M p , ε p))) 
                             (λ q → pairNil M (Ty M q)))

                        φ : (p : SlPl M τ) → SlOp M (snd (SlTy M p))
                        φ = fst pr

                        ψ : (p : SlPl M τ) → SlOp (Slice M) (φ p)
                        ψ = snd pr
                        
