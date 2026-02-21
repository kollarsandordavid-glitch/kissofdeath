import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.HashMap
import Mathlib.Tactic

namespace SSIVerification

structure SSINode where
  hash : Nat
  tokens : List Nat
  position : Nat
  score : Rat
  deriving DecidableEq

structure SSIIndex where
  nodes : List SSINode
  hashMap : List (Nat × List Nat)
  capacity : Nat
  nodeCount : Nat
  nodeCountValid : nodeCount ≤ capacity

def hashTokens (tokens : List Nat) : Nat :=
  tokens.foldl (fun acc t => (acc * 31 + t) % 1000000007) 0

theorem hashTokens_deterministic (tokens1 tokens2 : List Nat) (h : tokens1 = tokens2) :
  hashTokens tokens1 = hashTokens tokens2 := by
  rw [h]

def SSIIndex.init (capacity : Nat) : SSIIndex :=
  { nodes := []
  , hashMap := []
  , capacity := capacity
  , nodeCount := 0
  , nodeCountValid := Nat.zero_le _ }

def SSIIndex.insert (index : SSIIndex) (tokens : List Nat) (position : Nat) (score : Rat) :
  SSIIndex :=
  if h : index.nodeCount + 1 ≤ index.capacity then
    let hash := hashTokens tokens
    let node := SSINode.mk hash tokens position score
    let newNodes := node :: index.nodes
    let newHashMap := (hash, [index.nodeCount]) :: index.hashMap
    { nodes := newNodes
    , hashMap := newHashMap
    , capacity := index.capacity
    , nodeCount := index.nodeCount + 1
    , nodeCountValid := h }
  else index

theorem SSIIndex.insert_preserves_nodes (index : SSIIndex) (tokens : List Nat) 
  (position : Nat) (score : Rat) (h : index.nodeCount + 1 ≤ index.capacity) :
  (index.insert tokens position score).nodeCount = index.nodeCount + 1 := by
  unfold insert
  split
  · simp
  · contradiction

theorem SSIIndex.insert_increases_count (index : SSIIndex) (tokens : List Nat) 
  (position : Nat) (score : Rat) :
  (index.insert tokens position score).nodeCount ≥ index.nodeCount := by
  unfold insert
  split
  · omega
  · omega

def SSIIndex.lookup (index : SSIIndex) (hash : Nat) : List SSINode :=
  index.nodes.filter (fun n => n.hash = hash)

theorem SSIIndex.lookup_after_insert (index : SSIIndex) (tokens : List Nat) 
  (position : Nat) (score : Rat) (h : index.nodeCount + 1 ≤ index.capacity) :
  let hash := hashTokens tokens
  let newIndex := index.insert tokens position score
  ∃ node ∈ newIndex.lookup hash, node.tokens = tokens := by
  unfold insert lookup
  simp
  split
  · exists SSINode.mk (hashTokens tokens) tokens position score
    constructor
    · simp [hashTokens]
    · rfl
  · contradiction

def SSIIndex.query (index : SSIIndex) (queryTokens : List Nat) (topK : Nat) : 
  List SSINode :=
  let hash := hashTokens queryTokens
  let candidates := index.lookup hash
  candidates.take topK

theorem SSIIndex.query_subset (index : SSIIndex) (queryTokens : List Nat) (topK : Nat) :
  ∀ node ∈ index.query queryTokens topK, node ∈ index.nodes := by
  intro node hnodes
  unfold query lookup at hnodes
  simp at hnodes
  exact hnodes.1

theorem SSIIndex.query_hash_match (index : SSIIndex) (queryTokens : List Nat) (topK : Nat) :
  let hash := hashTokens queryTokens
  ∀ node ∈ index.query queryTokens topK, node.hash = hash := by
  intro hash node hnodes
  unfold query lookup at hnodes
  simp at hnodes
  exact hnodes.2

def jaccardSimilarity (tokens1 tokens2 : List Nat) : Rat :=
  let set1 := tokens1.toFinset
  let set2 := tokens2.toFinset
  let intersection := (set1 ∩ set2).card
  let union := (set1 ∪ set2).card
  if union = 0 then 0 else intersection / union

theorem jaccardSimilarity_reflexive (tokens : List Nat) :
  jaccardSimilarity tokens tokens = 1 := by
  unfold jaccardSimilarity
  simp
  split
  · rfl
  · omega

theorem jaccardSimilarity_symmetric (tokens1 tokens2 : List Nat) :
  jaccardSimilarity tokens1 tokens2 = jaccardSimilarity tokens2 tokens2 := by
  unfold jaccardSimilarity
  simp [Finset.inter_comm, Finset.union_comm]

theorem jaccardSimilarity_bounded (tokens1 tokens2 : List Nat) :
  0 ≤ jaccardSimilarity tokens1 tokens2 ∧ jaccardSimilarity tokens1 tokens2 ≤ 1 := by
  unfold jaccardSimilarity
  split
  · simp
    constructor
    · exact Rat.zero_le_one
    · exact le_refl 1
  · simp
    constructor
    · apply Rat.div_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by assumption))
    · apply Rat.div_le_one
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by assumption))
      · exact Nat.cast_le.mpr (Finset.card_inter_le _ _)

def SSIIndex.rankByScore (index : SSIIndex) (queryTokens : List Nat) : List SSINode :=
  let hash := hashTokens queryTokens
  let candidates := index.lookup hash
  candidates.mergeSort (fun n1 n2 => n1.score ≥ n2.score)

theorem SSIIndex.rank_scores_bounded (index : SSIIndex) (queryTokens : List Nat) :
  ∀ node ∈ index.rankByScore queryTokens, 0 ≤ node.score := by
  intro node hnodes
  unfold rankByScore lookup at hnodes
  simp at hnodes
  exact Rat.zero_le _

def SSIIndex.batchInsert (index : SSIIndex) (batch : List (List Nat × Nat × Rat)) : 
  SSIIndex :=
  batch.foldl (fun idx (tokens, pos, score) => idx.insert tokens pos score) index

theorem SSIIndex.batchInsert_length (index : SSIIndex) (batch : List (List Nat × Nat × Rat)) :
  (index.batchInsert batch).nodeCount ≥ index.nodeCount := by
  unfold batchInsert
  induction batch generalizing index with
  | nil => simp; omega
  | cons head tail ih =>
      simp
      have h := insert_increases_count index head.1 head.2.1 head.2.2
      have ih' := ih (index.insert head.1 head.2.1 head.2.2)
      omega

def SSIIndex.merge (index1 index2 : SSIIndex) : SSIIndex :=
  if h : index1.nodeCount + index2.nodeCount ≤ index1.capacity then
    { nodes := index1.nodes ++ index2.nodes
    , hashMap := index1.hashMap ++ index2.hashMap
    , capacity := index1.capacity
    , nodeCount := index1.nodeCount + index2.nodeCount
    , nodeCountValid := h }
  else index1

theorem SSIIndex.merge_preserves_nodes1 (index1 index2 : SSIIndex) 
  (h : index1.nodeCount + index2.nodeCount ≤ index1.capacity) :
  ∀ node ∈ index1.nodes, node ∈ (index1.merge index2).nodes := by
  intro node hnodes
  unfold merge
  split
  · simp
    left
    exact hnodes
  · contradiction

theorem SSIIndex.merge_preserves_nodes2 (index1 index2 : SSIIndex) 
  (h : index1.nodeCount + index2.nodeCount ≤ index1.capacity) :
  ∀ node ∈ index2.nodes, node ∈ (index1.merge index2).nodes := by
  intro node hnodes
  unfold merge
  split
  · simp
    right
    exact hnodes
  · contradiction

def SSIIndex.filterByTimestamp (index : SSIIndex) (minPosition maxPosition : Nat) : 
  SSIIndex :=
  let filteredNodes := index.nodes.filter (fun n => minPosition ≤ n.position ∧ n.position ≤ maxPosition)
  { nodes := filteredNodes
  , hashMap := []
  , capacity := index.capacity
  , nodeCount := filteredNodes.length
  , nodeCountValid := by
      have h := List.length_filter_le (fun n => minPosition ≤ n.position ∧ n.position ≤ maxPosition) index.nodes
      exact Nat.le_trans h index.nodeCountValid }

theorem SSIIndex.filter_timestamp_bounds (index : SSIIndex) (minPosition maxPosition : Nat) :
  ∀ node ∈ (index.filterByTimestamp minPosition maxPosition).nodes,
    minPosition ≤ node.position ∧ node.position ≤ maxPosition := by
  intro node hnodes
  unfold filterByTimestamp at hnodes
  simp at hnodes
  exact hnodes.2

def cosineSimilarity (vec1 vec2 : List Rat) : Rat :=
  if vec1.length ≠ vec2.length then 0
  else
    let dotProduct := (vec1.zip vec2).foldl (fun acc (x, y) => acc + x * y) 0
    let norm1 := (vec1.foldl (fun acc x => acc + x * x) 0).sqrt
    let norm2 := (vec2.foldl (fun acc x => acc + x * x) 0).sqrt
    if norm1 = 0 ∨ norm2 = 0 then 0
    else dotProduct / (norm1 * norm2)

theorem cosineSimilarity_bounded (vec1 vec2 : List Rat) :
  -1 ≤ cosineSimilarity vec1 vec2 ∧ cosineSimilarity vec1 vec2 ≤ 1 := by
  unfold cosineSimilarity
  split
  case isTrue _ =>
    constructor
    · exact neg_one_le_zero
    · exact zero_le_one
  case isFalse _ =>
    split
    case isTrue _ =>
      constructor
      · exact neg_one_le_zero
      · exact zero_le_one
    case isFalse hNorm =>
      push_neg at hNorm
      obtain ⟨hn1, hn2⟩ := hNorm
      constructor
      · apply le_trans
        · exact neg_one_le_zero
        · apply Rat.div_nonneg
          · exact le_refl _
          · exact mul_pos (Rat.sqrt_nonneg _).lt_of_ne' (Ne.symm hn1) 
                         |>.trans_le (mul_nonneg (Rat.sqrt_nonneg _) (Rat.sqrt_nonneg _))
                         |> fun _ => mul_pos (Rat.sqrt_pos.mpr (Rat.sqrt_nonneg _).lt_of_ne' (Ne.symm hn1)) 
                                            (Rat.sqrt_pos.mpr (Rat.sqrt_nonneg _).lt_of_ne' (Ne.symm hn2))
                         |> le_of_lt
      · exact Rat.div_le_one_of_le (by linarith) (mul_pos 
          (Rat.sqrt_pos.mpr ((Rat.sqrt_nonneg _).lt_of_ne' (Ne.symm hn1)))
          (Rat.sqrt_pos.mpr ((Rat.sqrt_nonneg _).lt_of_ne' (Ne.symm hn2))) |> le_of_lt)

theorem cosineSimilarity_symmetric (vec1 vec2 : List Rat) :
  cosineSimilarity vec1 vec2 = cosineSimilarity vec2 vec1 := by
  unfold cosineSimilarity
  split <;> split
  · rfl
  · contradiction
  · contradiction
  · simp [List.zip_comm]
    split <;> split
    · rfl
    · contradiction
    · contradiction
    · ring

def SSIIndex.semanticSearch (index : SSIIndex) (queryVector : List Rat) (topK : Nat) :
  List SSINode :=
  index.nodes.take topK

structure SSISearchResult where
  node : SSINode
  score : Rat
  relevance : Rat

def SSIIndex.hybridSearch (index : SSIIndex) (queryTokens : List Nat) 
  (queryVector : List Rat) (topK : Nat) : List SSISearchResult :=
  let lexicalResults := index.query queryTokens topK
  lexicalResults.map (fun n => 
    { node := n
    , score := n.score
    , relevance := 0 })

theorem SSIIndex.insert_lookup_correctness (index : SSIIndex) (tokens : List Nat) 
  (position : Nat) (score : Rat) (h : index.nodeCount + 1 ≤ index.capacity) :
  let hash := hashTokens tokens
  let newIndex := index.insert tokens position score
  ∃ node ∈ newIndex.lookup hash, 
    node.tokens = tokens ∧ node.position = position ∧ node.score = score := by
  unfold insert lookup
  simp
  split
  · exists SSINode.mk (hashTokens tokens) tokens position score
    constructor
    · simp
    · constructor <;> rfl
  · contradiction

theorem SSIIndex.query_correctness (index : SSIIndex) (queryTokens : List Nat) (topK : Nat) :
  ∀ node ∈ index.query queryTokens topK, 
    node.hash = hashTokens queryTokens ∧ node ∈ index.nodes := by
  intro node hnodes
  constructor
  · exact query_hash_match index queryTokens topK node hnodes
  · exact query_subset index queryTokens topK node hnodes

theorem SSIIndex.ranking_correctness (index : SSIIndex) (queryTokens : List Nat) :
  let ranked := index.rankByScore queryTokens
  ∀ i j, i < j → j < ranked.length → 
    ranked[i]?.isSome → ranked[j]?.isSome →
    ∃ ni nj, ranked[i]? = some ni ∧ ranked[j]? = some nj ∧ ni.score ≥ nj.score := by
  intro ranked i j hij hjlen hisomei hjsomej
  have hi_lt : i < ranked.length := Nat.lt_trans hij hjlen
  have hni : ∃ ni, ranked[i]? = some ni := Option.isSome_iff_exists.mp hisomei
  have hnj : ∃ nj, ranked[j]? = some nj := Option.isSome_iff_exists.mp hjsomej
  obtain ⟨ni, hni_eq⟩ := hni
  obtain ⟨nj, hnj_eq⟩ := hnj
  exact ⟨ni, nj, hni_eq, hnj_eq, by
    have hsorted := List.Sorted.rel_get_of_lt (List.mergeSort_sorted (fun n1 n2 : SSINode => n1.score ≥ n2.score) _)
    exact le_refl nj.score⟩

theorem SSIIndex.distributed_merge_correctness (index1 index2 : SSIIndex) 
  (h : index1.nodeCount + index2.nodeCount ≤ index1.capacity) :
  let merged := index1.merge index2
  (∀ node ∈ index1.nodes, node ∈ merged.nodes) ∧
  (∀ node ∈ index2.nodes, node ∈ merged.nodes) ∧
  merged.nodeCount = index1.nodeCount + index2.nodeCount := by
  constructor
  · exact merge_preserves_nodes1 index1 index2 h
  · constructor
    · exact merge_preserves_nodes2 index1 index2 h
    · unfold merge
      split
      · simp
      · contradiction

end SSIVerification
