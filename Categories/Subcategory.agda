{-# OPTIONS --universe-polymorphism #-}

open import Categories.Category hiding (module Heterogeneous)
open import Categories.Congruence

module Categories.Subcategory {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Relation.Binary using (Rel)
open import Data.Product using (_×_; _,_; map; zip; proj₁; proj₂)
open import Function using () renaming (_∘_ to _∙_)

open Category C
open Category.Equiv C

module Full {o'} (P : Obj → Set o') where

    record FullObj : Set ( o ⊔ o') where
      constructor fullobj
      field
        {A} : Obj
        .proof : P A

    full : Category (o ⊔ o') ℓ e
    full = record {
             Obj = FullObj;
             _⇒_ = λ x y → FullObj.A x ⇒ FullObj.A y;
             _≡_ = _≡_;
             id = id;
             _∘_ = _∘_;
             assoc = assoc;
             identityˡ =  identityˡ;
             identityʳ =  identityʳ;
             equiv =  equiv ;
             ∘-resp-≡ =  ∘-resp-≡ }


module Wide {ℓ'} (P : ∀ {A} {B} → A ⇒ B → Set ℓ') (P-id : ∀ {A} → P (id {A})) (P-∘ : ∀ {A B C} {g : B ⇒ C} {f : A ⇒ B} → P g → P f → P (g ∘ f)) where

    record Wide⇒ A B : Set (ℓ ⊔ ℓ') where
      constructor widearr
      field
        {f} : A ⇒ B
        .proof : P f

    full : Category (o ) (ℓ ⊔ ℓ') e
    full = record {
             Obj = Obj;
             _⇒_ = Wide⇒;
             _≡_ = _≡'_;
             id = widearr P-id;
             _∘_ =  λ f g → widearr (P-∘ (proof f) (proof g) );
             assoc = assoc;
             identityˡ =  identityˡ;
             identityʳ =  λ {A B F} → identityʳ {A} {B} ;
             equiv =  equiv';
             ∘-resp-≡ =  ∘-resp-≡ }
         where open Wide⇒
               import Relation.Binary
               _≡'_ : ∀ {A B} → (f g : Wide⇒ A B) → Set e
               F ≡' G = f F ≡ f G
               .equiv' : ∀ {A B} →  Relation.Binary.IsEquivalence (_≡'_ {A} {B})
               equiv' = record { refl =  refl; sym = sym; trans = trans }   --- Explicit to get eta-expansion polymorphism
