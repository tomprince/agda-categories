{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category hiding (module Heterogeneous)
open import Categories.Congruence

open import Categories.Functor using (Functor; _∘_)

module Categories.Arrow.AsNat {o ℓ e o' ℓ' e'} (C : Category o ℓ e) (D : Category o' ℓ' e') where

open import Level
open import Relation.Binary using (Rel)
open import Data.Product using (_×_; _,_; map; zip; proj₁; proj₂)
open import Function renaming (_∘_ to _∙_)
open import Categories.Arrow
open import Categories.NaturalTransformation


x : (f : Functor C (arrow D)) → NaturalTransformation (dom D ∘ f) (cod D ∘ f)
x f = record { η = ArrowObj.arr D ∙ F₀ ; commute = sym ∙ Arrow⇒.square  D ∙ F₁ }
  where open Categories.Functor.Functor f
        open Category.Equiv D

y : (F G : Functor C D) → (η : NaturalTransformation F G) → Functor C (arrow D)
y F G η = record {
            F₀ = λ x' → arrobj (η' x');
            F₁ = λ x' → arrarr (sym (commute x'));
            identity =  λ {x'} → identity F , identity G;
            homomorphism = λ {x'} →  homomorphism F , homomorphism G;
            F-resp-≡ = λ x' → (F-resp-≡ F x') , (F-resp-≡ G x') }
  where open Categories.Functor.Functor
        open ArrowObj D
        open Arrow⇒ D
        open Category.Equiv D
        open NaturalTransformation η renaming (η to η')
