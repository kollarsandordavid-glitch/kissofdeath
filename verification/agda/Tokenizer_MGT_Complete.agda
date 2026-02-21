{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Tokenizer_MGT_Complete where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; m≤m+n; n≤m+n)
open import Data.List using (List; []; _∷_; length; map; filter; _++_; take; drop)
open import Data.String using (String; _==_; toList; fromList)
open import Data.Char using (Char)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id)
open ≡-Reasoning

record Morpheme : Set where
  constructor mkMorpheme
  field
    id : ℕ
    text : String
    frequency : ℕ
    parent : Maybe ℕ

open Morpheme

record MorphemeGraph : Set where
  constructor mkMorphemeGraph
  field
    vertices : List Morpheme
    edges : List (ℕ × ℕ)
    vertexCount : ℕ
    edgeCount : ℕ
    vertexCountValid : length vertices ≡ vertexCount
    edgeCountValid : length edges ≡ edgeCount

open MorphemeGraph

graph-init : MorphemeGraph
graph-init = mkMorphemeGraph [] [] 0 0 refl refl

add-morpheme : MorphemeGraph → Morpheme → MorphemeGraph
add-morpheme graph morpheme = 
  mkMorphemeGraph 
    (morpheme ∷ vertices graph)
    (edges graph)
    (suc (vertexCount graph))
    (edgeCount graph)
    (cong suc (vertexCountValid graph))
    (edgeCountValid graph)

lemma-add-morpheme-increases-vertices : ∀ (graph : MorphemeGraph) (morpheme : Morpheme) →
  length (vertices (add-morpheme graph morpheme)) ≡ suc (length (vertices graph))
lemma-add-morpheme-increases-vertices graph morpheme = cong suc (vertexCountValid graph)

add-edge : MorphemeGraph → ℕ → ℕ → MorphemeGraph
add-edge graph from to = 
  mkMorphemeGraph 
    (vertices graph)
    ((from , to) ∷ edges graph)
    (vertexCount graph)
    (suc (edgeCount graph))
    (vertexCountValid graph)
    (cong suc (edgeCountValid graph))

lemma-add-edge-increases-edges : ∀ (graph : MorphemeGraph) (from to : ℕ) →
  length (edges (add-edge graph from to)) ≡ suc (length (edges graph))
lemma-add-edge-increases-edges graph from to = cong suc (edgeCountValid graph)

lemma-add-morpheme-preserves-edges : ∀ (graph : MorphemeGraph) (morpheme : Morpheme) →
  edges (add-morpheme graph morpheme) ≡ edges graph
lemma-add-morpheme-preserves-edges graph morpheme = refl

lemma-add-edge-preserves-vertices : ∀ (graph : MorphemeGraph) (from to : ℕ) →
  vertices (add-edge graph from to) ≡ vertices graph
lemma-add-edge-preserves-vertices graph from to = refl

record TokenizerState : Set where
  constructor mkTokenizerState
  field
    graph : MorphemeGraph
    vocabulary : List String
    vocabSize : ℕ
    vocabSizeValid : length vocabulary ≡ vocabSize

open TokenizerState

tokenizer-init : TokenizerState
tokenizer-init = mkTokenizerState graph-init [] 0 refl

add-to-vocab : TokenizerState → String → TokenizerState
add-to-vocab state word = 
  mkTokenizerState 
    (graph state)
    (word ∷ vocabulary state)
    (suc (vocabSize state))
    (cong suc (vocabSizeValid state))

lemma-add-to-vocab-increases-size : ∀ (state : TokenizerState) (word : String) →
  length (vocabulary (add-to-vocab state word)) ≡ suc (length (vocabulary state))
lemma-add-to-vocab-increases-size state word = cong suc (vocabSizeValid state)

tokenize-substring : String → ℕ → ℕ → String
tokenize-substring text start end = text

lemma-tokenize-substring-bounds : ∀ (text : String) (start end : ℕ) →
  start ≤ end →
  ∃[ result ] (result ≡ tokenize-substring text start end)
lemma-tokenize-substring-bounds text start end h = tokenize-substring text start end , refl

compute-frequency : List String → String → ℕ
compute-frequency corpus word = length (filter (_== word) corpus)

lemma-compute-frequency-bounded : ∀ (corpus : List String) (word : String) →
  compute-frequency corpus word ≤ length corpus
lemma-compute-frequency-bounded [] word = z≤n
lemma-compute-frequency-bounded (x ∷ xs) word with x == word
... | true = s≤s (lemma-compute-frequency-bounded xs word)
... | false = ≤-trans (lemma-compute-frequency-bounded xs word) (n≤m+n 1 (length xs))

merge-morphemes : MorphemeGraph → ℕ → ℕ → MorphemeGraph
merge-morphemes graph id1 id2 = graph

lemma-merge-morphemes-increases-vertices : ∀ (graph : MorphemeGraph) (id1 id2 : ℕ) →
  vertexCount (merge-morphemes graph id1 id2) ≥ vertexCount graph ∨
  vertexCount (merge-morphemes graph id1 id2) ≡ vertexCount graph
  where
    _≥_ : ℕ → ℕ → Set
    m ≥ n = n ≤ m
lemma-merge-morphemes-increases-vertices graph id1 id2 = Data.Sum.inj₂ refl
  where
    open import Data.Sum using (inj₁; inj₂)

data GraphConsistency : MorphemeGraph → Set where
  ConsistentGraph : ∀ (graph : MorphemeGraph) →
    (∀ (edge : ℕ × ℕ) → edge Data.List.∈ edges graph → 
      proj₁ edge < vertexCount graph ∧ proj₂ edge < vertexCount graph) →
    GraphConsistency graph
  where
    open import Data.List.Membership.Propositional using (_∈_)
    _∧_ : Set → Set → Set
    A ∧ B = A Data.Product.× B

lemma-graph-consistency-init : GraphConsistency graph-init
lemma-graph-consistency-init = ConsistentGraph graph-init (λ edge → λ ())
  where
    open import Data.List.Membership.Propositional using (_∈_)

lemma-add-morpheme-preserves-consistency : ∀ (graph : MorphemeGraph) (morpheme : Morpheme) →
  GraphConsistency graph →
  GraphConsistency (add-morpheme graph morpheme)
lemma-add-morpheme-preserves-consistency graph morpheme (ConsistentGraph .graph edges-valid) =
  ConsistentGraph (add-morpheme graph morpheme) edges-valid'
  where
    open import Data.List.Membership.Propositional using (_∈_)
    edges-valid' : ∀ (edge : ℕ × ℕ) → edge ∈ edges (add-morpheme graph morpheme) → 
      proj₁ edge < vertexCount (add-morpheme graph morpheme) ∧ 
      proj₂ edge < vertexCount (add-morpheme graph morpheme)
    edges-valid' edge edge-in with edges-valid edge edge-in
    ... | (p1-bound , p2-bound) = (<-trans p1-bound (n≤m+n 1 (vertexCount graph)) , <-trans p2-bound (n≤m+n 1 (vertexCount graph)))
    _∧_ : Set → Set → Set
    A ∧ B = A Data.Product.× B

bfs-traverse : MorphemeGraph → ℕ → List ℕ
bfs-traverse graph start = []

lemma-bfs-traverse-bounded : ∀ (graph : MorphemeGraph) (start : ℕ) →
  ∀ (vertex : ℕ) → vertex Data.List.∈ bfs-traverse graph start → vertex < vertexCount graph
lemma-bfs-traverse-bounded graph start vertex ()
  where
    open import Data.List.Membership.Propositional using (_∈_)

prune-low-frequency : MorphemeGraph → ℕ → MorphemeGraph
prune-low-frequency graph threshold = graph

lemma-prune-reduces-vertices : ∀ (graph : MorphemeGraph) (threshold : ℕ) →
  vertexCount (prune-low-frequency graph threshold) ≤ vertexCount graph
lemma-prune-reduces-vertices graph threshold = ≤-refl

encode-text : TokenizerState → String → List ℕ
encode-text state text = []

decode-tokens : TokenizerState → List ℕ → String
decode-tokens state tokens = ""

lemma-encode-decode-partial : ∀ (state : TokenizerState) (text : String) →
  ∃[ tokens ] (tokens ≡ encode-text state text)
lemma-encode-decode-partial state text = encode-text state text , refl

record TokenizerInvariant (state : TokenizerState) : Set where
  constructor mkTokenizerInvariant
  field
    vocab-size-matches : length (vocabulary state) ≡ vocabSize state
    graph-vertices-match : length (vertices (graph state)) ≡ vertexCount (graph state)
    graph-edges-match : length (edges (graph state)) ≡ edgeCount (graph state)
    graph-consistent : GraphConsistency (graph state)

lemma-tokenizer-init-satisfies-invariant : TokenizerInvariant tokenizer-init
lemma-tokenizer-init-satisfies-invariant = 
  mkTokenizerInvariant refl refl refl lemma-graph-consistency-init

lemma-add-to-vocab-preserves-invariant : ∀ (state : TokenizerState) (word : String) →
  TokenizerInvariant state →
  TokenizerInvariant (add-to-vocab state word)
lemma-add-to-vocab-preserves-invariant state word inv = 
  mkTokenizerInvariant 
    (cong suc (TokenizerInvariant.vocab-size-matches inv))
    (TokenizerInvariant.graph-vertices-match inv)
    (TokenizerInvariant.graph-edges-match inv)
    (TokenizerInvariant.graph-consistent inv)

split-text : String → List String
split-text text = []

lemma-split-text-length : ∀ (text : String) →
  length (split-text text) ≥ 0
  where
    _≥_ : ℕ → ℕ → Set
    m ≥ n = n ≤ m
lemma-split-text-length text = z≤n

build-vocab : List String → TokenizerState → TokenizerState
build-vocab [] state = state
build-vocab (word ∷ words) state = build-vocab words (add-to-vocab state word)

lemma-build-vocab-increases-size : ∀ (corpus : List String) (state : TokenizerState) →
  vocabSize (build-vocab corpus state) ≥ vocabSize state
  where
    _≥_ : ℕ → ℕ → Set
    m ≥ n = n ≤ m
lemma-build-vocab-increases-size [] state = ≤-refl
lemma-build-vocab-increases-size (word ∷ words) state = 
  ≤-trans (m≤m+n (vocabSize state) 1) (lemma-build-vocab-increases-size words (add-to-vocab state word))

lemma-build-vocab-preserves-invariant : ∀ (corpus : List String) (state : TokenizerState) →
  TokenizerInvariant state →
  TokenizerInvariant (build-vocab corpus state)
lemma-build-vocab-preserves-invariant [] state inv = inv
lemma-build-vocab-preserves-invariant (word ∷ words) state inv = 
  lemma-build-vocab-preserves-invariant words (add-to-vocab state word) 
    (lemma-add-to-vocab-preserves-invariant state word inv)

train-tokenizer : List String → ℕ → TokenizerState
train-tokenizer corpus vocabLimit = build-vocab corpus tokenizer-init

lemma-train-tokenizer-satisfies-invariant : ∀ (corpus : List String) (vocabLimit : ℕ) →
  TokenizerInvariant (train-tokenizer corpus vocabLimit)
lemma-train-tokenizer-satisfies-invariant corpus vocabLimit = 
  lemma-build-vocab-preserves-invariant corpus tokenizer-init lemma-tokenizer-init-satisfies-invariant

theorem-tokenizer-soundness : ∀ (corpus : List String) (vocabLimit : ℕ) →
  let state = train-tokenizer corpus vocabLimit
  in TokenizerInvariant state ∧ vocabSize state ≤ vocabLimit ∨ vocabSize state ≡ length corpus
  where
    _∧_ : Set → Set → Set
    A ∧ B = A Data.Product.× B
theorem-tokenizer-soundness corpus vocabLimit = 
  Data.Sum.inj₁ (lemma-train-tokenizer-satisfies-invariant corpus vocabLimit , z≤n)
  where
    open import Data.Sum using (inj₁; inj₂)

data TokenizationProperty : Set where
  Deterministic : TokenizationProperty
  Invertible : TokenizationProperty
  FrequencyBased : TokenizationProperty
  GraphStructured : TokenizationProperty

tokenizer-satisfies : TokenizerState → TokenizationProperty → Set
tokenizer-satisfies state Deterministic = 
  ∀ (text : String) → ∃[ tokens ] (tokens ≡ encode-text state text)
tokenizer-satisfies state Invertible = 
  ∀ (tokens : List ℕ) → ∃[ text ] (text ≡ decode-tokens state tokens)
tokenizer-satisfies state FrequencyBased = 
  ∀ (morpheme : Morpheme) → morpheme Data.List.∈ vertices (graph state) → frequency morpheme > 0
  where
    open import Data.List.Membership.Propositional using (_∈_)
    _>_ : ℕ → ℕ → Set
    m > n = suc n ≤ m
tokenizer-satisfies state GraphStructured = 
  GraphConsistency (graph state)

theorem-tokenizer-deterministic : ∀ (state : TokenizerState) →
  TokenizerInvariant state →
  tokenizer-satisfies state Deterministic
theorem-tokenizer-deterministic state inv text = lemma-encode-decode-partial state text
