
import ConnesRigidity.PropertyTExactCertificateOrbitRadixCheckers

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open scoped BigOperators

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitBlockDimensions_sum :
    (∑ block : Fin 28, blockDimension block.val) = 424 := by
  unfold blockDimension dataEntry blockMetadataData
  decide +kernel

theorem orbitBlockRowStart_eq_prefix_sum (block : Fin 28) :
    blockRowStart block.val =
      ∑ previous : Fin block.val,
        blockDimension (Fin.castLE block.isLt.le previous).val := by
  revert block
  unfold blockRowStart blockDimension dataEntry blockMetadataData
  decide +kernel

noncomputable def orbitBlockFinEquiv :
    (Σ block : Fin 28, Fin (blockDimension block.val)) ≃ Fin 424 :=
  finSigmaFinEquiv.trans (finCongr orbitBlockDimensions_sum)

@[simp] theorem orbitBlockFinEquiv_apply_val
    (index : Σ block : Fin 28, Fin (blockDimension block.val)) :
    (orbitBlockFinEquiv index).val =
      blockRowStart index.1.val + index.2.val := by
  simp only [orbitBlockFinEquiv, Equiv.trans_apply, finCongr_apply,
    Fin.val_cast, finSigmaFinEquiv_apply]
  rw [orbitBlockRowStart_eq_prefix_sum]

theorem orbitBlockRowStart_add_lt
    (block : Fin 28) (offset : Fin (blockDimension block.val)) :
    blockRowStart block.val + offset.val < 424 := by
  rw [← orbitBlockFinEquiv_apply_val ⟨block, offset⟩]
  exact (orbitBlockFinEquiv ⟨block, offset⟩).isLt

theorem orbitBlock_sum_eq_fin_sum
    {α : Type*} [AddCommMonoid α] (f : Fin 424 → α) :
    (∑ block : Fin 28, ∑ offset : Fin (blockDimension block.val),
      f ⟨blockRowStart block.val + offset.val,
        orbitBlockRowStart_add_lt block offset⟩) =
      ∑ row : Fin 424, f row := by
  classical
  calc
    _ = ∑ index : Σ block : Fin 28, Fin (blockDimension block.val),
          f (orbitBlockFinEquiv index) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro block _
      apply Finset.sum_congr rfl
      intro offset _
      congr 1
      exact Fin.ext (orbitBlockFinEquiv_apply_val ⟨block, offset⟩).symm
    _ = _ := orbitBlockFinEquiv.sum_comp f

theorem orbitFin_sum_eq_block_sum
    {α : Type*} [AddCommMonoid α] (f : Fin 424 → α) :
    (∑ row : Fin 424, f row) =
      ∑ block : Fin 28, ∑ offset : Fin (blockDimension block.val),
        f ⟨blockRowStart block.val + offset.val,
          orbitBlockRowStart_add_lt block offset⟩ :=
  (orbitBlock_sum_eq_fin_sum f).symm

theorem orbitBlockOfColumn_eq_of_metadata_check
    (block : Fin 28) (offset : Fin (blockDimension block.val))
    (hcheck : orbitRadixBlockColumnMetadataRowCheck block.val offset.val = true) :
    blockOfColumn (blockRowStart block.val + offset.val) = block.val ∧
      blockOffsetOfColumn (blockRowStart block.val + offset.val) = offset.val := by
  exact (orbitRadixBlockColumnMetadataRowCheck_sound
    block.val offset.val hcheck).2.2

theorem orbitBlock_metadata
    (block : Fin 28) (offset : Fin (blockDimension block.val)) :
    blockOfColumn (blockRowStart block.val + offset.val) = block.val ∧
      blockOffsetOfColumn (blockRowStart block.val + offset.val) = offset.val := by
  revert offset block
  unfold blockDimension blockRowStart blockOfColumn blockOffsetOfColumn
    dataEntry blockMetadataData blockColumnData
  decide +kernel

end ConnesRigidity.AffineSymplecticOrbitCertificate
