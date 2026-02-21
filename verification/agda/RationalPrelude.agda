{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module RationalPrelude where

open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _/_) public
open import Data.Rational.Properties as ℚP public

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning) public
open ≡-Reasoning public
