


import ConnesRigidity.PropertyTExactCertificateOrbitRadixNormSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitRadixSoundness
import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers









namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators



noncomputable def orbitBlockWeight (block : Fin 28) :
    Matrix (Fin 424) (Fin (blockDimension block.val)) ℚ :=
  fun row column =>
    (scaledInverseEntryInt
      (blockRowStart block.val + column.val) row.val : ℚ)

@[simp] theorem orbitBlockWeight_apply
    (block : Fin 28) (row : Fin 424)
    (column : Fin (blockDimension block.val)) :
    orbitBlockWeight block row column =
      (scaledInverseEntryInt
        (blockRowStart block.val + column.val) row.val : ℚ) := rfl




@[simp] theorem orbitRadixBase_eq_radixBase :
    orbitRadixBase = radixBase := rfl



theorem orbitRadixReducedGramEncoding_eq_encode (row : Nat) :
    orbitRadixReducedGramEncoding row =
      orbitRadixEncode
        ((List.range 424).map fun column =>
          gramEntry (row + 1) (column + 1)) := by
  unfold orbitRadixReducedGramEncoding orbitRadixEncode
  rw [List.foldr_map]
  rfl



theorem orbitBlockWeight_gram_apply
    (block : Fin 28) (row column : Fin 424) :
    (orbitBlockWeight block * blockGram block.val *
        (orbitBlockWeight block).transpose) row column =
      (orbitRadixBlockComputedEntry block.val row column : ℚ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    orbitBlockWeight_apply, blockGram_apply,
    orbitRadixBlockComputedEntry]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro offset _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro other _
  ring



theorem orbitBlockWeight_sum_gram_apply
    (row column : Fin 424) :
    (∑ block : Fin 28,
      orbitBlockWeight block * blockGram block.val *
        (orbitBlockWeight block).transpose) row column =
      (orbitRadixComputedEntry row column : ℚ) := by
  change (∑ block : Fin 28,
    (orbitBlockWeight block * blockGram block.val *
      (orbitBlockWeight block).transpose) row column) = _
  simp_rw [orbitBlockWeight_gram_apply]
  simp [orbitRadixComputedEntry]



theorem orbitRadix_integer_identity_of_packed
    (packed : ∀ row : Fin 424,
      orbitRadixEncode
          ((List.finRange 424).map (orbitRadixComputedEntry row)) =
        congruenceInverseScale ^ 2 *
          orbitRadixEncode
            ((List.finRange 424).map fun column =>
              gramEntry (row.val + 1) (column.val + 1)))
    (bounds : ∀ row column : Fin 424,
      -radixBase < orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) ∧
        orbitRadixComputedEntry row column -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (column.val + 1) < radixBase) :
    ∀ row column : Fin 424,
      orbitRadixComputedEntry row column =
        congruenceInverseScale ^ 2 *
          gramEntry (row.val + 1) (column.val + 1) := by
  intro row column
  let expected : Fin 424 → Int := fun other =>
    congruenceInverseScale ^ 2 *
      gramEntry (row.val + 1) (other.val + 1)
  have digitBounds : List.Forall₂
      (fun x y => -orbitRadixBase < x - y ∧ x - y < orbitRadixBase)
      ((List.finRange 424).map (orbitRadixComputedEntry row))
      ((List.finRange 424).map expected) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro other _
    change -orbitRadixBase <
        orbitRadixComputedEntry row other -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (other.val + 1) ∧
      orbitRadixComputedEntry row other -
          congruenceInverseScale ^ 2 *
            gramEntry (row.val + 1) (other.val + 1) < orbitRadixBase
    simpa [orbitRadixBase_eq_radixBase] using bounds row other
  have rowEquality :
      (List.finRange 424).map (orbitRadixComputedEntry row) =
        (List.finRange 424).map expected := by
    apply orbitRadixEncode_injective_of_difference_bound digitBounds
    have expectedEncoding :
        orbitRadixEncode ((List.finRange 424).map expected) =
          congruenceInverseScale ^ 2 *
            orbitRadixEncode
              ((List.finRange 424).map fun other =>
                gramEntry (row.val + 1) (other.val + 1)) := by
      simpa [expected, List.map_map, Function.comp_def] using
        orbitRadixEncode_map_mul (congruenceInverseScale ^ 2)
          ((List.finRange 424).map fun other =>
            gramEntry (row.val + 1) (other.val + 1))
    rw [expectedEncoding]
    exact packed row
  have pairwise : List.Forall₂
      (fun first second : Fin 424 =>
        orbitRadixComputedEntry row first = expected second)
      (List.finRange 424) (List.finRange 424) := by
    have mappedEquality : List.Forall₂ (fun x y : Int => x = y)
        ((List.finRange 424).map (orbitRadixComputedEntry row))
        ((List.finRange 424).map expected) := by
      rw [rowEquality]
      exact List.forall₂_refl _
    exact List.forall₂_map_right_iff.mp
      (List.forall₂_map_left_iff.mp mappedEquality)
  exact (List.forall₂_same.mp pairwise) column (by simp)



theorem orbitReducedGram_radix_identity_of_integer
    (integerIdentity : ∀ row column : Fin 424,
      orbitRadixComputedEntry row column =
        congruenceInverseScale ^ 2 *
          gramEntry (row.val + 1) (column.val + 1)) :
    ∀ row column : Fin 424,
      (∑ block : Fin 28,
        orbitBlockWeight block * blockGram block.val *
          (orbitBlockWeight block).transpose) row column =
        (256 : ℚ) ^ 2 *
          (gramEntry (row.val + 1) (column.val + 1) : ℚ) := by
  intro row column
  rw [orbitBlockWeight_sum_gram_apply, integerIdentity]
  norm_num [congruenceInverseScale]

end ConnesRigidity.AffineSymplecticOrbitCertificate
