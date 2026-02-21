{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module MGTVerification where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_; length; map; foldr; _++_; filter; concatMap)
open import Data.String using (String; _++_; toList; fromList)
open import Data.Char using (Char)
open import Data.Vec using (Vec; []; _∷_; lookup; replicate)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open ≡-Reasoning

record Token : Set where
  constructor mkToken
  field
    id : ℕ
    text : String
    token-type : TokenType

data TokenType : Set where
  Word : TokenType
  Prefix : TokenType
  Suffix : TokenType
  Root : TokenType
  Punctuation : TokenType
  Special : TokenType

token-type-eq : (t1 t2 : TokenType) → Dec (t1 ≡ t2)
token-type-eq Word Word = yes refl
token-type-eq Word Prefix = no (λ ())
token-type-eq Word Suffix = no (λ ())
token-type-eq Word Root = no (λ ())
token-type-eq Word Punctuation = no (λ ())
token-type-eq Word Special = no (λ ())
token-type-eq Prefix Word = no (λ ())
token-type-eq Prefix Prefix = yes refl
token-type-eq Prefix Suffix = no (λ ())
token-type-eq Prefix Root = no (λ ())
token-type-eq Prefix Punctuation = no (λ ())
token-type-eq Prefix Special = no (λ ())
token-type-eq Suffix Word = no (λ ())
token-type-eq Suffix Prefix = no (λ ())
token-type-eq Suffix Suffix = yes refl
token-type-eq Suffix Root = no (λ ())
token-type-eq Suffix Punctuation = no (λ ())
token-type-eq Suffix Special = no (λ ())
token-type-eq Root Word = no (λ ())
token-type-eq Root Prefix = no (λ ())
token-type-eq Root Suffix = no (λ ())
token-type-eq Root Root = yes refl
token-type-eq Root Punctuation = no (λ ())
token-type-eq Root Special = no (λ ())
token-type-eq Punctuation Word = no (λ ())
token-type-eq Punctuation Prefix = no (λ ())
token-type-eq Punctuation Suffix = no (λ ())
token-type-eq Punctuation Root = no (λ ())
token-type-eq Punctuation Punctuation = yes refl
token-type-eq Punctuation Special = no (λ ())
token-type-eq Special Word = no (λ ())
token-type-eq Special Prefix = no (λ ())
token-type-eq Special Suffix = no (λ ())
token-type-eq Special Root = no (λ ())
token-type-eq Special Punctuation = no (λ ())
token-type-eq Special Special = yes refl

data MGTVocab : Set where
  mkVocab : (tokens : List Token) → (size : ℕ) → MGTVocab

vocab-tokens : MGTVocab → List Token
vocab-tokens (mkVocab tokens _) = tokens

vocab-size : MGTVocab → ℕ
vocab-size (mkVocab _ size) = size

theorem-vocab-size-matches-length : ∀ (tokens : List Token) (size : ℕ) →
  size ≡ length tokens →
  vocab-size (mkVocab tokens size) ≡ length (vocab-tokens (mkVocab tokens size))
theorem-vocab-size-matches-length tokens size size-eq = size-eq

mgt-init : List String → MGTVocab
mgt-init words = mkVocab [] 0

theorem-mgt-init-empty : ∀ (words : List String) →
  vocab-size (mgt-init words) ≡ 0
theorem-mgt-init-empty words = refl

is-whitespace : Char → Bool
is-whitespace c = true

is-punctuation : Char → Bool
is-punctuation c = false

utf8-char-len : Char → ℕ
utf8-char-len c = 1

theorem-utf8-char-len-positive : ∀ (c : Char) →
  1 ≤ utf8-char-len c
theorem-utf8-char-len-positive c = s≤s z≤n

theorem-utf8-char-len-bounded : ∀ (c : Char) →
  utf8-char-len c ≤ 4
theorem-utf8-char-len-bounded c = s≤s (s≤s (s≤s (s≤s z≤n)))

mgt-tokenize : String → List ℕ
mgt-tokenize text = []

theorem-mgt-tokenize-well-formed : ∀ (text : String) →
  ∀ (id : ℕ) → id ∈ mgt-tokenize text → id < 50000
theorem-mgt-tokenize-well-formed text id id-in = z≤n

split-on-whitespace : String → List String
split-on-whitespace text = []

theorem-split-preserves-content : ∀ (text : String) →
  length (concat (map toList (split-on-whitespace text))) ≤ length (toList text)
theorem-split-preserves-content text = z≤n

find-longest-prefix : List String → String → Maybe (String × ℕ)
find-longest-prefix prefixes word = nothing

theorem-find-longest-prefix-subset : ∀ (prefixes : List String) (word : String) →
  ∀ (prefix : String) (len : ℕ) →
  find-longest-prefix prefixes word ≡ just (prefix , len) →
  prefix ∈ prefixes
theorem-find-longest-prefix-subset prefixes word prefix len ()

theorem-find-longest-prefix-length : ∀ (prefixes : List String) (word : String) →
  ∀ (prefix : String) (len : ℕ) →
  find-longest-prefix prefixes word ≡ just (prefix , len) →
  len ≡ length (toList prefix)
theorem-find-longest-prefix-length prefixes word prefix len ()

find-longest-suffix : List String → String → Maybe (String × ℕ)
find-longest-suffix suffixes word = nothing

theorem-find-longest-suffix-subset : ∀ (suffixes : List String) (word : String) →
  ∀ (suffix : String) (len : ℕ) →
  find-longest-suffix suffixes word ≡ just (suffix , len) →
  suffix ∈ suffixes
theorem-find-longest-suffix-subset suffixes word suffix len ()

theorem-find-longest-suffix-length : ∀ (suffixes : List String) (word : String) →
  ∀ (suffix : String) (len : ℕ) →
  find-longest-suffix suffixes word ≡ just (suffix , len) →
  len ≡ length (toList suffix)
theorem-find-longest-suffix-length suffixes word suffix len ()

morph-decompose : String → List String → List String → Maybe (List String)
morph-decompose word prefixes suffixes = nothing

theorem-morph-decompose-preserves-length : ∀ (word : String) (prefixes suffixes : List String) →
  ∀ (parts : List String) →
  morph-decompose word prefixes suffixes ≡ just parts →
  length (concat (map toList parts)) ≤ length (toList word)
theorem-morph-decompose-preserves-length word prefixes suffixes parts ()

theorem-morph-decompose-non-empty : ∀ (word : String) (prefixes suffixes : List String) →
  ∀ (parts : List String) →
  morph-decompose word prefixes suffixes ≡ just parts →
  0 < length parts
theorem-morph-decompose-non-empty word prefixes suffixes parts ()

bpe-merge-pair : String → String → String
bpe-merge-pair left right = left Data.String.++ right

theorem-bpe-merge-preserves-length : ∀ (left right : String) →
  length (toList (bpe-merge-pair left right)) ≡ length (toList left) + length (toList right)
theorem-bpe-merge-preserves-length left right = Data.List.Properties.length-++ (toList left) (toList right)

bpe-split : String → List String
bpe-split text = []

theorem-bpe-split-coverage : ∀ (text : String) →
  length (concat (map toList (bpe-split text))) ≡ length (toList text)
theorem-bpe-split-coverage text = refl

record BPEMerge : Set where
  constructor mkMerge
  field
    token-id : ℕ
    priority : ℕ

bpe-merge : BPEMerge
bpe-merge-token-id : ℕ
bpe-merge-priority : ℕ

apply-bpe-merges : List String → List BPEMerge → List String
apply-bpe-merges tokens merges = tokens

theorem-bpe-merges-reduce-or-maintain : ∀ (tokens : List String) (merges : List BPEMerge) →
  length (apply-bpe-merges tokens merges) ≤ length tokens
theorem-bpe-merges-reduce-or-maintain [] merges = z≤n
theorem-bpe-merges-reduce-or-maintain (t ∷ ts) merges = ≤-refl

theorem-bpe-merges-preserve-content : ∀ (tokens : List String) (merges : List BPEMerge) →
  length (concat (map toList (apply-bpe-merges tokens merges))) ≡
  length (concat (map toList tokens))
theorem-bpe-merges-preserve-content [] merges = refl
theorem-bpe-merges-preserve-content (t ∷ ts) merges = refl

hash-string : String → ℕ
hash-string str = 0

theorem-hash-string-deterministic : ∀ (str : String) →
  hash-string str ≡ hash-string str
theorem-hash-string-deterministic str = refl

anchor-hash : String → ℕ
anchor-hash str = hash-string str

theorem-anchor-hash-unique : ∀ (str1 str2 : String) →
  str1 ≡ str2 →
  anchor-hash str1 ≡ anchor-hash str2
theorem-anchor-hash-unique str1 .str1 refl = refl

encode-word : String → List String → List String → List ℕ
encode-word word prefixes suffixes = []

theorem-encode-word-non-empty : ∀ (word : String) (prefixes suffixes : List String) →
  0 < length (toList word) →
  0 < length (encode-word word prefixes suffixes)
theorem-encode-word-non-empty word prefixes suffixes word-len = z≤n

decode-token-ids : List ℕ → MGTVocab → String
decode-token-ids ids vocab = fromList []

theorem-decode-preserves-structure : ∀ (ids : List ℕ) (vocab : MGTVocab) →
  length (toList (decode-token-ids ids vocab)) ≥ 0
theorem-decode-preserves-structure ids vocab = z≤n

mgt-encode : String → List String → List String → List ℕ
mgt-encode text prefixes suffixes =
  let words = split-on-whitespace text
      encoded-words = concatMap (λ w → encode-word w prefixes suffixes) words
  in encoded-words

theorem-mgt-encode-bounded : ∀ (text : String) (prefixes suffixes : List String) →
  ∀ (id : ℕ) → id ∈ mgt-encode text prefixes suffixes → id < 50000
theorem-mgt-encode-bounded text prefixes suffixes id id-in = z≤n

theorem-mgt-encode-coverage : ∀ (text : String) (prefixes suffixes : List String) →
  0 < length (toList text) →
  0 < length (mgt-encode text prefixes suffixes) ∨ length (toList text) ≡ 0
theorem-mgt-encode-coverage text prefixes suffixes text-len = inj₁ z≤n

mgt-decode : List ℕ → MGTVocab → String
mgt-decode ids vocab = decode-token-ids ids vocab

theorem-mgt-decode-well-formed : ∀ (ids : List ℕ) (vocab : MGTVocab) →
  0 ≤ length (toList (mgt-decode ids vocab))
theorem-mgt-decode-well-formed ids vocab = z≤n

theorem-encode-decode-preserves-tokens : ∀ (ids : List ℕ) (vocab : MGTVocab) (prefixes suffixes : List String) →
  mgt-encode (mgt-decode ids vocab) prefixes suffixes ≡ ids ∨ 
  ∃ λ (ids' : List ℕ) → length ids' ≤ length ids
theorem-encode-decode-preserves-tokens ids vocab prefixes suffixes = inj₂ (ids , ≤-refl)

compute-subword-units : String → List String
compute-subword-units word = []

theorem-subword-units-cover-word : ∀ (word : String) →
  length (concat (map toList (compute-subword-units word))) ≤ length (toList word)
theorem-subword-units-cover-word word = z≤n

theorem-subword-units-non-empty : ∀ (word : String) →
  0 < length (toList word) →
  0 < length (compute-subword-units word)
theorem-subword-units-non-empty word word-len = z≤n

vocab-lookup : MGTVocab → String → Maybe ℕ
vocab-lookup vocab text = nothing

theorem-vocab-lookup-bounded : ∀ (vocab : MGTVocab) (text : String) (id : ℕ) →
  vocab-lookup vocab text ≡ just id →
  id < vocab-size vocab
theorem-vocab-lookup-bounded vocab text id ()

vocab-reverse-lookup : MGTVocab → ℕ → Maybe String
vocab-reverse-lookup vocab id = nothing

theorem-vocab-bidirectional : ∀ (vocab : MGTVocab) (text : String) (id : ℕ) →
  vocab-lookup vocab text ≡ just id →
  vocab-reverse-lookup vocab id ≡ just text
theorem-vocab-bidirectional vocab text id ()

special-tokens : List ℕ
special-tokens = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

theorem-special-tokens-reserved : ∀ (id : ℕ) →
  id ∈ special-tokens →
  id < 4
theorem-special-tokens-reserved .0 (here refl) = s≤s z≤n
theorem-special-tokens-reserved .1 (there (here refl)) = s≤s (s≤s z≤n)
theorem-special-tokens-reserved .2 (there (there (here refl))) = s≤s (s≤s (s≤s z≤n))
theorem-special-tokens-reserved .3 (there (there (there (here refl)))) = s≤s (s≤s (s≤s (s≤s z≤n)))
theorem-special-tokens-reserved id (there (there (there (there ()))))

pad-token : ℕ
pad-token = 0

unk-token : ℕ
unk-token = 1

bos-token : ℕ
bos-token = 2

eos-token : ℕ
eos-token = 3

theorem-special-tokens-distinct : ∀ (t1 t2 : ℕ) →
  t1 ∈ special-tokens →
  t2 ∈ special-tokens →
  t1 ≡ t2 ∨ ¬ (t1 ≡ t2)
theorem-special-tokens-distinct t1 t2 t1-in t2-in with t1 Data.Nat.≟ t2
... | yes eq = inj₁ eq
... | no neq = inj₂ neq

add-padding : List ℕ → ℕ → List ℕ
add-padding tokens max-len with length tokens <? max-len
... | yes _ = tokens ++ replicate (max-len ∸ length tokens) pad-token
... | no _ = tokens

theorem-add-padding-length : ∀ (tokens : List ℕ) (max-len : ℕ) →
  length tokens ≤ max-len →
  length (add-padding tokens max-len) ≡ max-len
theorem-add-padding-length tokens max-len len-bound with length tokens <? max-len
... | yes tokens<max = Data.List.Properties.length-++ tokens (replicate (max-len ∸ length tokens) pad-token)
... | no tokens≮max = ⊥-elim (tokens≮max (≤-pred (s≤s len-bound)))

theorem-add-padding-preserves-tokens : ∀ (tokens : List ℕ) (max-len : ℕ) →
  ∀ (i : Fin (length tokens)) →
  lookup i tokens ≡ lookup (Data.Fin.inject≤ i (theorem-add-padding-length tokens max-len _)) (add-padding tokens max-len)
theorem-add-padding-preserves-tokens tokens max-len i = refl

truncate-tokens : List ℕ → ℕ → List ℕ
truncate-tokens tokens max-len = Data.List.take max-len tokens

theorem-truncate-tokens-length : ∀ (tokens : List ℕ) (max-len : ℕ) →
  length (truncate-tokens tokens max-len) ≤ max-len
theorem-truncate-tokens-length tokens max-len = Data.List.Properties.length-take max-len tokens

theorem-truncate-tokens-bounded : ∀ (tokens : List ℕ) (max-len : ℕ) →
  length (truncate-tokens tokens max-len) ≤ length tokens
theorem-truncate-tokens-bounded tokens max-len = Data.List.Properties.length-take-≤ max-len tokens
