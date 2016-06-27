{-# OPTIONS --without-K #-}

open import HoTT
open import opetopes.simple.Monads

module opetopes.simple.Opetopes where

  open Monad

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
  drop = (unit , unit) , ext unit

  glob : Opetope 2
  glob = (unit , unit) , (int unit unit (λ p → unit) (λ p → snd (drop)))

  simplex : Opetope 2
  simplex = (unit , unit) , (int unit unit (λ p → unit) (λ p → snd (glob)))

  NSlice : ℕ → Monad → Monad
  NSlice O M = M
  NSlice (S n) M = Slice (NSlice n M)

  MOp : ℕ → Monad → Type₀
  MOp n M = Frm (NSlice n M )

  mobj : (M : Monad) → (i : Frm M) → MOp 0 M
  mobj M i = i

  marrow : (M : Monad) → (i : Frm M) → (c : Op M i) → MOp 1 M
  marrow M i c = i , μ M i c (λ p → η M (Ty M p)) -- And *this* is normal form!

  mdrop : (M : Monad) → (i : Frm M) → MOp 2 M
  mdrop M i = (i , η M i) , (ext i)

  mglob : (M : Monad) → (i : Frm M) → (c : Op M i) → MOp 2 M
  mglob M i c = (i , μ M i c (λ p → η M (Ty M p))) , int i c (λ p → η M (Ty M p) ) (λ p → snd (mdrop M _))

  msimplex : (M : Monad) → (i : Frm M) → (c : Op M i) → (δ : (p : Pl M c) → Op M (Ty M p)) → MOp 2 M
  msimplex M i c δ = (i , (μ M i c (λ p → μ M (Ty M p) (δ p) (λ q → η M (Ty M q))))) , 
                     int i c (λ p → μ M (Ty M p) (δ p) (λ q → η M (Ty M q))) (λ p → snd (mglob M (Ty M p) (δ p)))


  mdblhorn : (M : Monad) → (i : Frm M) → (c : Op M i) → (δ : (p : Pl M c) → Op M (Ty M p)) → MOp 3 M
  mdblhorn M i c δ = ((_ , _) , _) , 
                     (int _ (snd (msimplex M i c δ)) 
                          (λ { (this .i .c _ _) → η (Slice M) (i , c) ; 
                               (that .i .c _ _ p (this .(Ty M p) .(δ p) _ _)) → η (Slice M) (Ty M p , δ p) ; 
                               (that .i .c _ _ p (that .(Ty M p) .(δ p) _ _ p₁ ())) }) 
                          (λ { (this .i .c _ _) → ext (i , c) ; 
                               (that .i .c _ _ p (this .(Ty M p) .(δ p) _ _)) → ext (Ty M p , δ p) ; 
                               (that .i .c _ _ p (that .(Ty M p) .(δ p) _ _ p₁ ())) }))
