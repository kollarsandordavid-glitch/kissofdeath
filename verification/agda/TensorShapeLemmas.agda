{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module TensorShapeLemmas where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_)
open import Data.Nat.Properties
open import Data.List using (List; []; _∷_; length; product; map; foldr; sum; _++_; replicate)
open import Data.List.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open ≡-Reasoning

shape-size : List ℕ → ℕ
shape-size [] = 1
shape-size (d ∷ ds) = d * shape-size ds

lemma-shape-size-nil : shape-size [] ≡ 1
lemma-shape-size-nil = refl

lemma-shape-size-singleton : ∀ (n : ℕ) → shape-size (n ∷ []) ≡ n
lemma-shape-size-singleton n = *-identityʳ n

lemma-shape-size-cons : ∀ (d : ℕ) (ds : List ℕ) →
  shape-size (d ∷ ds) ≡ d * shape-size ds
lemma-shape-size-cons d ds = refl

lemma-shape-size-++ : ∀ (sh1 sh2 : List ℕ) →
  shape-size (sh1 ++ sh2) ≡ shape-size sh1 * shape-size sh2
lemma-shape-size-++ [] sh2 = sym (+-identityʳ (shape-size sh2))
lemma-shape-size-++ (d ∷ sh1) sh2 = begin
  d * shape-size (sh1 ++ sh2)
    ≡⟨ cong (d *_) (lemma-shape-size-++ sh1 sh2) ⟩
  d * (shape-size sh1 * shape-size sh2)
    ≡⟨ sym (*-assoc d (shape-size sh1) (shape-size sh2)) ⟩
  (d * shape-size sh1) * shape-size sh2 ∎

lemma-shape-size-replicate : ∀ (n d : ℕ) →
  shape-size (Data.List.replicate n d) ≡ power d n
  where
    power : ℕ → ℕ → ℕ
    power d zero = 1
    power d (suc n) = d * power d n
lemma-shape-size-replicate zero d = refl
lemma-shape-size-replicate (suc n) d = cong (d *_) (lemma-shape-size-replicate n d)

lemma-shape-size-map : ∀ (f : ℕ → ℕ) (sh : List ℕ)
  (preserves-mul : ∀ x y → f (x * y) ≡ f x * f y) (preserves-1 : f 1 ≡ 1) →
  shape-size (Data.List.map f sh) ≡ f (shape-size sh)
lemma-shape-size-map f [] preserves-mul preserves-1 = sym preserves-1
lemma-shape-size-map f (d ∷ sh) preserves-mul preserves-1 = begin
  f d * shape-size (Data.List.map f sh)
    ≡⟨ cong (f d *_) (lemma-shape-size-map f sh preserves-mul preserves-1) ⟩
  f d * f (shape-size sh)
    ≡⟨ sym (preserves-mul d (shape-size sh)) ⟩
  f (d * shape-size sh) ∎

lemma-shape-size-positive : ∀ (sh : List ℕ) (all-positive : ∀ (d : ℕ) → d ∈ sh → d > 0) →
  shape-size sh > 0
  where
    _∈_ : ℕ → List ℕ → Set
    x ∈ [] = ⊥
    x ∈ (y ∷ ys) = (x ≡ y) ⊎ (x ∈ ys)
    
    _⊎_ : Set → Set → Set
    A ⊎ B = Data.Sum._⊎_ A B
    
    ⊥ : Set
    ⊥ = Data.Empty.⊥
    
    inj₁ : {A B : Set} → A → A ⊎ B
    inj₁ = Data.Sum.inj₁
    
    inj₂ : {A B : Set} → B → A ⊎ B
    inj₂ = Data.Sum.inj₂
lemma-shape-size-positive [] all-positive = s≤s z≤n
lemma-shape-size-positive (d ∷ sh) all-positive =
  *-mono-< (all-positive d (inj₁ refl)) (lemma-shape-size-positive sh (λ x x∈sh → all-positive x (inj₂ x∈sh)))
  where
    inj₁ : {A B : Set} → A → Data.Sum._⊎_ A B
    inj₁ = Data.Sum.inj₁
    
    inj₂ : {A B : Set} → B → Data.Sum._⊎_ A B
    inj₂ = Data.Sum.inj₂
    
    *-mono-< : ∀ {a b c d} → a < b → c < d → a * c < b * d
    *-mono-< {zero} {suc b} {zero} {suc d} a<b c<d = s≤s z≤n
    *-mono-< {zero} {suc b} {suc c} {suc d} a<b c<d = s≤s z≤n
    *-mono-< {suc a} {suc b} {zero} {suc d} a<b c<d = s≤s z≤n
    *-mono-< {suc a} {suc b} {suc c} {suc d} (s≤s a≤b) (s≤s c≤d) = s≤s (+-mono-≤ (*-mono-≤ a≤b (s≤s c≤d)) (≤-step (≤-step z≤n)))

lemma-shape-size-commutative-factor : ∀ (d1 d2 : ℕ) (sh : List ℕ) →
  shape-size ((d1 * d2) ∷ sh) ≡ shape-size (d1 ∷ d2 ∷ sh)
lemma-shape-size-commutative-factor d1 d2 sh = *-assoc d1 d2 (shape-size sh)

lemma-shape-flatten : ∀ (sh : List ℕ) → shape-size sh ≡ shape-size (shape-size sh ∷ [])
lemma-shape-flatten sh = sym (*-identityʳ (shape-size sh))

lemma-shape-broadcast-compatible : ∀ (sh1 sh2 : List ℕ) →
  (length sh1 ≡ length sh2) →
  (∀ i → lookup-safe sh1 i ≡ 1 ⊎ lookup-safe sh2 i ≡ 1 ⊎ lookup-safe sh1 i ≡ lookup-safe sh2 i) →
  shape-size (broadcast-shape sh1 sh2) ≡ max (shape-size sh1) (shape-size sh2)
  where
    lookup-safe : List ℕ → ℕ → ℕ
    lookup-safe [] _ = 0
    lookup-safe (x ∷ xs) zero = x
    lookup-safe (x ∷ xs) (suc i) = lookup-safe xs i
    
    broadcast-shape : List ℕ → List ℕ → List ℕ
    broadcast-shape [] [] = []
    broadcast-shape (d1 ∷ sh1) (d2 ∷ sh2) =
      (if d1 ≡ᵇ 1 then d2 else if d2 ≡ᵇ 1 then d1 else d1) ∷ broadcast-shape sh1 sh2
      where
        _≡ᵇ_ : ℕ → ℕ → Bool
        zero ≡ᵇ zero = true
        zero ≡ᵇ suc m = false
        suc n ≡ᵇ zero = false
        suc n ≡ᵇ suc m = n ≡ᵇ m
        
        Bool : Set
        Bool = Data.Bool.Bool
        
        true : Bool
        true = Data.Bool.true
        
        false : Bool
        false = Data.Bool.false
    broadcast-shape _ _ = []
    
    max : ℕ → ℕ → ℕ
    max zero m = m
    max (suc n) zero = suc n
    max (suc n) (suc m) = suc (max n m)
    
    _⊎_ : Set → Set → Set
    A ⊎ B = Data.Sum._⊎_ A B
lemma-shape-broadcast-compatible [] [] len-eq compat = refl
lemma-shape-broadcast-compatible (d1 ∷ sh1) [] len-eq compat = ⊥-elim (zero≢suc len-eq)
  where
    zero≢suc : ∀ {n} → zero ≡ suc n → ⊥
    zero≢suc ()
    
    ⊥-elim : {A : Set} → ⊥ → A
    ⊥-elim = Data.Empty.⊥-elim
    
    ⊥ : Set
    ⊥ = Data.Empty.⊥
lemma-shape-broadcast-compatible [] (d2 ∷ sh2) len-eq compat = ⊥-elim (suc≢zero len-eq)
  where
    suc≢zero : ∀ {n} → suc n ≡ zero → ⊥
    suc≢zero ()
    
    ⊥-elim : {A : Set} → ⊥ → A
    ⊥-elim = Data.Empty.⊥-elim
    
    ⊥ : Set
    ⊥ = Data.Empty.⊥
