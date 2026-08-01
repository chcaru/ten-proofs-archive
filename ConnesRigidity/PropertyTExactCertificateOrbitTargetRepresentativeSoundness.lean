
import ConnesRigidity.PropertyTExactCertificateOrbitTargetCoefficients
import ConnesRigidity.PropertyTExactCertificateOrbitTargetWitness

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem targetSeekGroup_seek_tail_of_lt
    (groups : List (List Int)) {current code : Int}
    (hcode : current < code) :
    targetSeekGroup code (targetSeekGroup current groups).2 =
      targetSeekGroup code groups := by
  induction groups with
  | nil => rfl
  | cons group groups inductionHypothesis =>
      change
        targetSeekGroup code
            (if group.getD 0 0 < current then
              targetSeekGroup current groups
            else if group.getD 0 0 = current then
              (group.getD 2 0, groups)
            else
              (0, group :: groups)).2 =
          if group.getD 0 0 < code then
            targetSeekGroup code groups
          else if group.getD 0 0 = code then
            (group.getD 2 0, groups)
          else
            (0, group :: groups)
      by_cases hcurrent : group.getD 0 0 < current
      · have hfuture : group.getD 0 0 < code := by omega
        simpa only [hcurrent, hfuture, ↓reduceIte, Prod.snd] using
          inductionHypothesis
      · by_cases hequal : group.getD 0 0 = current
        · have hfuture : group.getD 0 0 < code := by omega
          rw [if_neg hcurrent, if_pos hequal, if_pos hfuture]
        · have hnotEqual : group.getD 0 0 ≠ current := hequal
          simp only [hcurrent, hnotEqual, ↓reduceIte]
          rfl

theorem targetGroupCheck_seek_nonnegative {α : Type*}
    (key : α → Int) {previous : Int} {position : Nat}
    {groups : List (List Int)} {products : List α}
    (hcheck : targetGroupCheck key previous position groups products = true)
    (code : Int) :
    0 ≤ (targetSeekGroup code groups).1 := by
  induction groups generalizing previous position products with
  | nil => simp [targetSeekGroup]
  | cons group groups inductionHypothesis =>
      simp only [targetGroupCheck] at hcheck
      split at hcheck
      next hshape =>
        split at hcheck
        next hnone => contradiction
        next remaining hconsume =>
          change
            0 ≤
              (if group.getD 0 0 < code then
                targetSeekGroup code groups
              else if group.getD 0 0 = code then
                (group.getD 2 0, groups)
              else
                (0, group :: groups)).1
          by_cases hless : group.getD 0 0 < code
          · simp only [hless, ↓reduceIte]
            exact inductionHypothesis hcheck
          · by_cases hequal : group.getD 0 0 = code
            · rw [if_neg hless, if_pos hequal]
              exact le_of_lt hshape.2.2.2
            · simp only [hless, hequal, ↓reduceIte]
              exact le_rfl
      next hshape => contradiction

theorem orbitTargetRepresentativeRowsCheck_get
    (rows groups : List (List Int)) (previous : Int)
    (start index : Nat) (hindex : index < rows.length)
    (hcheck :
      orbitTargetRepresentativeRowsCheck previous start rows groups = true) :
    let record := rows.getD index []
    let orbit := record.getD 0 0
    let code := record.getD 1 0
    let representative := coefficientRepresentativeData.getD orbit.toNat #[]
    let witness := coefficientTargetWitnessData.getD orbit.toNat #[]
    record.length = 2 ∧
      (0 ≤ orbit ∧ orbit < (995 : Int)) ∧
      previous < code ∧
      (targetRepresentativeCodeIndexData.getD orbit.toNat []).getD
        0 (-1) = (start + index : Nat) ∧
      representative.size = 20 ∧
      targetCoordinateBounds representative.toList = true ∧
      isSymplecticRow representative = true ∧
      targetCoordinateCode representative.toList = code ∧
      witness.size = 3 ∧
      witness.getD 0 0 =
        (if (basisData.getD 0 #[]) == representative then 1 else 0) ∧
      witness.getD 1 0 =
        generatorData.toList.foldl
          (fun count generator =>
            if generator == representative then count + 1 else count)
          0 ∧
      witness.getD 2 0 = (targetSeekGroup code groups).1 := by
  induction rows generalizing previous start index groups with
  | nil => simp at hindex
  | cons row rows inductionHypothesis =>
      simp only [orbitTargetRepresentativeRowsCheck, Bool.and_eq_true] at hcheck
      have hhead := orbitTargetRepresentativeRecordCheck_sound
        previous start row groups hcheck.1
      cases index with
      | zero =>
          simpa [orbitTargetSeekProductGroup] using hhead
      | succ index =>
          have htailIndex : index < rows.length := by simpa using hindex
          have htail := inductionHypothesis
            (groups :=
              (orbitTargetSeekProductGroup (row.getD 1 0) groups).2)
            (previous := row.getD 1 0) (start := start + 1)
            (index := index) htailIndex hcheck.2
          dsimp at htail ⊢
          simp only [List.getD_cons_succ] at ⊢
          rcases htail with
            ⟨hlength, horbit, hcode, hinverse, hsize, hbounds, hvalid,
              hrepresentativeCode, hwitnessSize, hidentity, hgenerator,
              hproduct⟩
          refine ⟨hlength, horbit, ?_, ?_, hsize, hbounds, hvalid,
            hrepresentativeCode, hwitnessSize, hidentity, hgenerator, ?_⟩
          · have hprevious := hhead.2.2.1
            omega
          · omega
          · rw [← targetSeekGroup_seek_tail_of_lt groups hcode]
            exact hproduct

theorem orbitTargetRepresentativeRowsCheck_orbit
    (orbit : Fin 995)
    (hinverseSize : targetRepresentativeCodeIndexData.length = 995)
    (hrowsSize : targetRepresentativeCodeSortedData.length = 995)
    (hinverse :
      orbitTargetRepresentativeInverseCheck 0
        targetRepresentativeCodeIndexData = true)
    (hrows :
      orbitTargetRepresentativeRowsCheck (-1) 0
        targetRepresentativeCodeSortedData
          targetGeneratorProductGroupData = true) :
    let representative := coefficientRepresentativeData.getD orbit.val #[]
    let witness := coefficientTargetWitnessData.getD orbit.val #[]
    representative.size = 20 ∧
      targetCoordinateBounds representative.toList = true ∧
      isSymplecticRow representative = true ∧
      witness.size = 3 ∧
      witness.getD 0 0 =
        (if (basisData.getD 0 #[]) == representative then 1 else 0) ∧
      witness.getD 1 0 =
        generatorData.toList.foldl
          (fun count generator =>
            if generator == representative then count + 1 else count)
          0 ∧
      witness.getD 2 0 =
        (targetSeekGroup (targetCoordinateCode representative.toList)
          targetGeneratorProductGroupData).1 := by
  have horbitIndex : orbit.val < targetRepresentativeCodeIndexData.length := by
    omega
  have hposition := orbitTargetRepresentativeInverseCheck_get
    targetRepresentativeCodeIndexData 0 orbit.val horbitIndex hinverse
  dsimp at hposition
  obtain ⟨hpositionNonnegative, hpositionBound, hrecordOrbit⟩ := hposition
  let position :=
    (targetRepresentativeCodeIndexData.getD orbit.val []).getD 0 (-1)
  have hpositionIndex : position.toNat <
      targetRepresentativeCodeSortedData.length := by
    have hbound : position.toNat < 995 := by omega
    omega
  have hrow := orbitTargetRepresentativeRowsCheck_get
    targetRepresentativeCodeSortedData targetGeneratorProductGroupData
      (-1) 0 position.toNat hpositionIndex hrows
  dsimp at hrow
  have hrecordOrbitNat :
      ((targetRepresentativeCodeSortedData.getD position.toNat []).getD
        0 0).toNat = orbit.val := by
    have heq :
        (targetRepresentativeCodeSortedData.getD position.toNat []).getD
          0 0 = (orbit.val : Int) := by
      simpa [position] using hrecordOrbit
    exact_mod_cast congrArg Int.toNat heq
  rw [hrecordOrbitNat] at hrow
  rcases hrow with
    ⟨_, _, _, _, hsize, hbounds, hvalid, hcode, hwitnessSize,
      hidentity, hgenerator, hproduct⟩
  dsimp
  refine ⟨hsize, hbounds, hvalid, hwitnessSize, hidentity, hgenerator, ?_⟩
  rw [hcode]
  exact hproduct

theorem orbitTargetRepresentativeRowsCheck_identity
    (orbit : Fin 995)
    (hinverseSize : targetRepresentativeCodeIndexData.length = 995)
    (hrowsSize : targetRepresentativeCodeSortedData.length = 995)
    (hinverse :
      orbitTargetRepresentativeInverseCheck 0
        targetRepresentativeCodeIndexData = true)
    (hrows :
      orbitTargetRepresentativeRowsCheck (-1) 0
        targetRepresentativeCodeSortedData
          targetGeneratorProductGroupData = true) :
    targetGroupIndicator (1 : constructedGammaZeroGroup)
        (coefficientRepresentativeElement orbit.val) =
      orbitTargetWitnessIdentity orbit.val := by
  have hrow := orbitTargetRepresentativeRowsCheck_orbit orbit
    hinverseSize hrowsSize hinverse hrows
  dsimp at hrow
  obtain ⟨hsize, _, hvalid, _, hidentity, _, _⟩ := hrow
  unfold orbitTargetWitnessIdentity dataEntry coefficientRepresentativeElement
    targetGroupIndicator
  rw [hidentity]
  by_cases hequal :
      (1 : constructedGammaZeroGroup) =
        gammaZeroOfRow (coefficientRepresentativeData.getD orbit.val #[])
  · have hboolean := (targetIdentityRawRow_beq_iff hsize hvalid).mpr hequal
    rw [if_pos hequal, hboolean]
    rfl
  · have hboolean :
        ((basisData.getD 0 #[]) ==
          (coefficientRepresentativeData.getD orbit.val #[])) = false := by
      cases h :
          ((basisData.getD 0 #[]) ==
            (coefficientRepresentativeData.getD orbit.val #[])) with
      | false => rfl
      | true => exact (hequal
          ((targetIdentityRawRow_beq_iff hsize hvalid).mp h)).elim
    rw [if_neg hequal, hboolean]
    rfl

theorem orbitTargetRepresentativeRowsCheck_generator
    (orbit : Fin 995)
    (hinverseSize : targetRepresentativeCodeIndexData.length = 995)
    (hrowsSize : targetRepresentativeCodeSortedData.length = 995)
    (hinverse :
      orbitTargetRepresentativeInverseCheck 0
        targetRepresentativeCodeIndexData = true)
    (hrows :
      orbitTargetRepresentativeRowsCheck (-1) 0
        targetRepresentativeCodeSortedData
          targetGeneratorProductGroupData = true) :
    targetGeneratorMultiplicity gammaZeroElementaryGenerators
        (coefficientRepresentativeElement orbit.val) =
      orbitTargetWitnessGeneratorMultiplicity orbit.val := by
  have hrow := orbitTargetRepresentativeRowsCheck_orbit orbit
    hinverseSize hrowsSize hinverse hrows
  dsimp at hrow
  obtain ⟨hsize, _, hvalid, _, _, hgenerator, _⟩ := hrow
  unfold orbitTargetWitnessGeneratorMultiplicity dataEntry
    coefficientRepresentativeElement targetGeneratorMultiplicity
    targetGroupIndicator
  rw [hgenerator, targetGeneratorRawFold_eq_finset_sum _ hsize hvalid]
  apply Finset.sum_congr rfl
  intro generator _
  split_ifs <;> rfl

theorem orbitTargetRepresentativeRowsCheck_product_seek
    (orbit : Fin 995)
    (hinverseSize : targetRepresentativeCodeIndexData.length = 995)
    (hrowsSize : targetRepresentativeCodeSortedData.length = 995)
    (hinverse :
      orbitTargetRepresentativeInverseCheck 0
        targetRepresentativeCodeIndexData = true)
    (hrows :
      orbitTargetRepresentativeRowsCheck (-1) 0
        targetRepresentativeCodeSortedData
          targetGeneratorProductGroupData = true) :
    orbitTargetWitnessProductMultiplicity orbit.val =
      (targetSeekGroup
        (targetCoordinateCode
          (coefficientRepresentativeData.getD orbit.val #[]).toList)
        targetGeneratorProductGroupData).1 := by
  have hrow := orbitTargetRepresentativeRowsCheck_orbit orbit
    hinverseSize hrowsSize hinverse hrows
  exact hrow.2.2.2.2.2.2

theorem orbitTargetRepresentativeWitness_semantics
    (orbit : Fin 995) (hcheck : orbitTargetStreamingCheck = true) :
    targetGroupIndicator (1 : constructedGammaZeroGroup)
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessIdentity orbit.val ∧
      targetGeneratorMultiplicity gammaZeroElementaryGenerators
          (coefficientRepresentativeElement orbit.val) =
        orbitTargetWitnessGeneratorMultiplicity orbit.val ∧
      (targetGeneratorProductRowData.countP
        (fun row => decide
          (row.getD 22 0 =
            targetCoordinateCode
              (coefficientRepresentativeData.getD orbit.val #[]).toList)) :
          Int) =
        orbitTargetWitnessProductMultiplicity orbit.val := by
  obtain ⟨_, _, hrowsSize, hinverseSize, _, _, _, _, _, hinverse,
    hgroups, hrows⟩ := orbitTargetStreamingCheck_sound hcheck
  refine ⟨orbitTargetRepresentativeRowsCheck_identity orbit
    hinverseSize hrowsSize hinverse hrows,
    orbitTargetRepresentativeRowsCheck_generator orbit
      hinverseSize hrowsSize hinverse hrows, ?_⟩
  let code :=
    targetCoordinateCode
      (coefficientRepresentativeData.getD orbit.val #[]).toList
  have hseek := orbitTargetRepresentativeRowsCheck_product_seek orbit
    hinverseSize hrowsSize hinverse hrows
  have hcount := targetGroupCheck_seek_countP
    (fun row : List Int => row.getD 22 0) hgroups code
  have hnonnegative := targetGroupCheck_seek_nonnegative
    (fun row : List Int => row.getD 22 0) hgroups code
  change
    (targetGeneratorProductRowData.countP
      (fun row => decide (row.getD 22 0 = code)) : Int) =
        orbitTargetWitnessProductMultiplicity orbit.val
  change orbitTargetWitnessProductMultiplicity orbit.val =
    (targetSeekGroup code targetGeneratorProductGroupData).1 at hseek
  rw [hseek, hcount, Int.toNat_of_nonneg hnonnegative]

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
