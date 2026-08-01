
import ConnesRigidity.PropertyTExactCertificateCoefficientFactorBridge

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

private theorem range_map_getD
    {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      change
        (List.range (l.length + 1)).map
            (fun i => (a :: l).getD i d) =
          a :: l
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.getD_cons_zero, List.map_map]
      change
        a :: (List.range l.length).map (fun i => l.getD i d) =
          a :: l
      exact congrArg (a :: ·) ih

private theorem range_map_getD_map
    {α β : Type*} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun i => f (l.getD i d)) =
      l.map f := by
  change
    (List.range l.length).map (f ∘ fun i => l.getD i d) =
      l.map f
  rw [← List.map_map, range_map_getD]

private theorem flatten_map_flatMap
    {α β : Type*} (chunks : List (List α)) (f : α → List β) :
    (chunks.map fun chunk => chunk.flatMap f).flatten =
      chunks.flatten.flatMap f := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_append, ih]

private theorem coefficientNegativeTermChunks_flatten :
    ((List.range 20).map coefficientNegativeTermChunk).flatten =
      negativeEdgeTerms := by
  rw [show 20 = coefficientNegativeEdgeChunks.length by
    simp [coefficientNegativeEdgeChunks, coefficientNegativeChunkSizes]]
  unfold coefficientNegativeTermChunk
  rw [range_map_getD_map coefficientNegativeEdgeChunks []
    (fun chunk => chunk.flatMap negativeEdgeTermRow)]
  rw [flatten_map_flatMap]
  unfold coefficientNegativeEdgeChunks negativeEdgeTerms
  rw [List.flatten_splitLengths]
  unfold coefficientNegativeChunkSizes negativeEdges negativeEdgeData
  decide +kernel

private theorem coefficientPositiveTermChunks_flatten :
    ((List.range 18).map coefficientPositiveTermChunk).flatten =
      positiveEdgeTerms := by
  rw [show 18 = coefficientPositiveEdgeChunks.length by
    simp [coefficientPositiveEdgeChunks, coefficientPositiveChunkSizes]]
  unfold coefficientPositiveTermChunk
  rw [range_map_getD_map coefficientPositiveEdgeChunks []
    (fun chunk => chunk.flatMap positiveEdgeTermRow)]
  rw [flatten_map_flatMap]
  unfold coefficientPositiveEdgeChunks positiveEdgeTerms
  rw [List.flatten_splitLengths]
  unfold coefficientPositiveChunkSizes positiveEdges positiveEdgeData
  decide +kernel

set_option maxHeartbeats 0 in

theorem coefficientSourceChunks_flatten :
    coefficientSourceChunks.flatten = certificateTerms := by
  rw [coefficientSourceChunks, certificateTerms, List.flatten_append,
    List.flatten_append, List.flatten_append,
    coefficientFactorTermChunks_flatten,
    coefficientNegativeTermChunks_flatten,
    coefficientPositiveTermChunks_flatten]
  simp

end AffineSymplecticCertificate

end ConnesRigidity
