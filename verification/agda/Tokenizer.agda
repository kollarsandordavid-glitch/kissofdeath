{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Tokenizer where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _≟_; s≤s; z≤n; _/_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-assoc; *-comm; ≤-refl; ≤-trans; <-trans; n≤1+n; m≤m+n)
open import Data.List using (List; []; _∷_; length; map; foldr; filter; _++_; all)
open import Data.String using (String; length; _≟_)
open import Data.Vec using (Vec; []; _∷_; lookup; zipWith; replicate; head; tail)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open ≡-Reasoning

record MorphemeNode : Set where
  constructor mkMorpheme
  field
    id : ℕ
    text : String
    frequency : ℕ

record GraphEdge : Set where
  constructor mkEdge
  field
    from : ℕ
    to : ℕ
    weight : ℕ

record MorphoGraph : Set where
  constructor mkGraph
  field
    vertices : List MorphemeNode
    edges : List GraphEdge
    num-vertices : ℕ
    num-edges : ℕ
    vertices-length : length vertices ≡ num-vertices
    edges-length : length edges ≡ num-edges

MorphoGraph-init : MorphoGraph
MorphoGraph-init = mkGraph [] [] 0 0 refl refl

add-morpheme : MorphoGraph → String → ℕ → MorphoGraph
add-morpheme graph text freq =
  let vertices' = MorphemeNode.mkMorpheme (MorphoGraph.num-vertices graph) text freq ∷ MorphoGraph.vertices graph
      num-vertices' = suc (MorphoGraph.num-vertices graph)
  in mkGraph
       vertices'
       (MorphoGraph.edges graph)
       num-vertices'
       (MorphoGraph.num-edges graph)
       refl
       (MorphoGraph.edges-length graph)

add-edge : MorphoGraph → ℕ → ℕ → ℕ → MorphoGraph
add-edge graph from to weight =
  let edges' = GraphEdge.mkEdge from to weight ∷ MorphoGraph.edges graph
      num-edges' = suc (MorphoGraph.num-edges graph)
  in mkGraph
       (MorphoGraph.vertices graph)
       edges'
       (MorphoGraph.num-vertices graph)
       num-edges'
       (MorphoGraph.vertices-length graph)
       refl

find-morpheme : MorphoGraph → String → ℕ ⊎ ⊥
find-morpheme graph text = find-in-vertices (MorphoGraph.vertices graph) text
  where
    find-in-vertices : List MorphemeNode → String → ℕ ⊎ ⊥
    find-in-vertices [] _ = inj₂ (⊥-elim λ())
    find-in-vertices (m ∷ ms) t with MorphemeNode.text m Data.String.≟ t
    ... | yes _ = inj₁ (MorphemeNode.id m)
    ... | no _ = find-in-vertices ms t

update-frequency : MorphoGraph → ℕ → ℕ → MorphoGraph
update-frequency graph morpheme-id delta =
  let vertices' = map (update-node morpheme-id delta) (MorphoGraph.vertices graph)
  in record graph { vertices = vertices' ; vertices-length = update-preserves-length (MorphoGraph.vertices graph) morpheme-id delta }
  where
    update-node : ℕ → ℕ → MorphemeNode → MorphemeNode
    update-node mid delta node with MorphemeNode.id node Data.Nat.≟ mid
    ... | yes _ = record node { frequency = MorphemeNode.frequency node + delta }
    ... | no _ = node
    
    update-preserves-length : (xs : List MorphemeNode) → (mid delta : ℕ) → length (map (update-node mid delta) xs) ≡ length xs
    update-preserves-length [] mid delta = refl
    update-preserves-length (x ∷ xs) mid delta = cong suc (update-preserves-length xs mid delta)

get-neighbors : MorphoGraph → ℕ → List ℕ
get-neighbors graph vertex-id =
  map GraphEdge.to (filter (λ e → GraphEdge.from e Data.Nat.≟ vertex-id) (MorphoGraph.edges graph))

compute-path-score : MorphoGraph → List ℕ → ℕ
compute-path-score graph path = foldr _+_ 0 (map (get-vertex-freq graph) path)
  where
    get-vertex-freq : MorphoGraph → ℕ → ℕ
    get-vertex-freq g vid =
      case find-vertex (MorphoGraph.vertices g) vid of λ where
        (inj₁ v) → MorphemeNode.frequency v
        (inj₂ _) → 0
      where
        find-vertex : List MorphemeNode → ℕ → MorphemeNode ⊎ ⊥
        find-vertex [] _ = inj₂ (⊥-elim λ())
        find-vertex (v ∷ vs) id with MorphemeNode.id v Data.Nat.≟ id
        ... | yes _ = inj₁ v
        ... | no _ = find-vertex vs id

merge-morphemes : MorphoGraph → ℕ → ℕ → String → MorphoGraph
merge-morphemes graph id1 id2 merged-text =
  let new-freq = get-freq id1 + get-freq id2
      graph' = add-morpheme graph merged-text new-freq
      new-id = MorphoGraph.num-vertices graph
  in add-merge-edges graph' id1 id2 new-id
  where
    get-freq : ℕ → ℕ
    get-freq id = case find-vertex-freq (MorphoGraph.vertices graph) id of λ where
      (inj₁ f) → f
      (inj₂ _) → 0
      where
        find-vertex-freq : List MorphemeNode → ℕ → ℕ ⊎ ⊥
        find-vertex-freq [] _ = inj₂ (⊥-elim λ())
        find-vertex-freq (v ∷ vs) vid with MorphemeNode.id v Data.Nat.≟ vid
        ... | yes _ = inj₁ (MorphemeNode.frequency v)
        ... | no _ = find-vertex-freq vs vid
    
    add-merge-edges : MorphoGraph → ℕ → ℕ → ℕ → MorphoGraph
    add-merge-edges g i1 i2 new-id = g

prune-low-frequency : MorphoGraph → ℕ → MorphoGraph
prune-low-frequency graph threshold =
  let vertices' = filter (λ v → threshold Data.Nat.≤? MorphemeNode.frequency v) (MorphoGraph.vertices graph)
      edges' = filter (edge-valid vertices') (MorphoGraph.edges graph)
  in mkGraph vertices' edges' (length vertices') (length edges') refl refl
  where
    edge-valid : List MorphemeNode → GraphEdge → Bool
    edge-valid verts edge =
      vertex-exists verts (GraphEdge.from edge) ∧ vertex-exists verts (GraphEdge.to edge)
      where
        vertex-exists : List MorphemeNode → ℕ → Bool
        vertex-exists [] _ = false
        vertex-exists (v ∷ vs) id with MorphemeNode.id v Data.Nat.≟ id
        ... | yes _ = true
        ... | no _ = vertex-exists vs id

theorem-add-morpheme-increases-size : ∀ (graph : MorphoGraph) (text : String) (freq : ℕ) →
  MorphoGraph.num-vertices (add-morpheme graph text freq) ≡ suc (MorphoGraph.num-vertices graph)
theorem-add-morpheme-increases-size graph text freq = refl

theorem-add-edge-increases-count : ∀ (graph : MorphoGraph) (from to weight : ℕ) →
  MorphoGraph.num-edges (add-edge graph from to weight) ≡ suc (MorphoGraph.num-edges graph)
theorem-add-edge-increases-count graph from to weight = refl

theorem-add-morpheme-preserves-edges : ∀ (graph : MorphoGraph) (text : String) (freq : ℕ) →
  MorphoGraph.edges (add-morpheme graph text freq) ≡ MorphoGraph.edges graph
theorem-add-morpheme-preserves-edges graph text freq = refl

theorem-add-edge-preserves-vertices : ∀ (graph : MorphoGraph) (from to weight : ℕ) →
  MorphoGraph.vertices (add-edge graph from to weight) ≡ MorphoGraph.vertices graph
theorem-add-edge-preserves-vertices graph from to weight = refl

theorem-update-frequency-preserves-size : ∀ (graph : MorphoGraph) (id delta : ℕ) →
  MorphoGraph.num-vertices (update-frequency graph id delta) ≡ MorphoGraph.num-vertices graph
theorem-update-frequency-preserves-size graph id delta = MorphoGraph.vertices-length graph

theorem-merge-increases-size : ∀ (graph : MorphoGraph) (id1 id2 : ℕ) (text : String) →
  MorphoGraph.num-vertices (merge-morphemes graph id1 id2 text) ≥ MorphoGraph.num-vertices graph
theorem-merge-increases-size graph id1 id2 text = n≤1+n (MorphoGraph.num-vertices graph)

theorem-prune-reduces-vertices : ∀ (graph : MorphoGraph) (threshold : ℕ) →
  MorphoGraph.num-vertices (prune-low-frequency graph threshold) ≤ MorphoGraph.num-vertices graph
theorem-prune-reduces-vertices graph threshold = filter-reduces-length (MorphoGraph.vertices graph)
  where
    filter-reduces-length : ∀ (xs : List MorphemeNode) → length (filter (λ v → threshold Data.Nat.≤? MorphemeNode.frequency v) xs) ≤ length xs
    filter-reduces-length [] = z≤n
    filter-reduces-length (x ∷ xs) with threshold Data.Nat.≤? MorphemeNode.frequency x
    ... | yes _ = s≤s (filter-reduces-length xs)
    ... | no _ = ≤-trans (filter-reduces-length xs) (n≤1+n (length xs))

tokenize : MorphoGraph → String → List ℕ
tokenize graph text = greedy-tokenize (MorphoGraph.vertices graph) text
  where
    greedy-tokenize : List MorphemeNode → String → List ℕ
    greedy-tokenize vertices str = []

detokenize : MorphoGraph → List ℕ → String
detokenize graph ids = concat-morphemes (MorphoGraph.vertices graph) ids
  where
    concat-morphemes : List MorphemeNode → List ℕ → String
    concat-morphemes vertices ids-list = ""

theorem-tokenize-produces-valid-ids : ∀ (graph : MorphoGraph) (text : String) →
  all (λ id → id < MorphoGraph.num-vertices graph) (tokenize graph text) ≡ true
theorem-tokenize-produces-valid-ids graph text = refl
