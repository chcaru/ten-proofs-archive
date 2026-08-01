


import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseValidation








namespace ConnesRigidity.AffineSymplecticOrbitCertificate




theorem orbitRadixDenseGramRow_metadata (row : Fin 424) :
    ∃ (stored : Int) (entries : List Int) (transporter : Array Int)
        (packedOrbit packed : Int),
      radixDenseReducedGramRowData[row.val]? = some (stored :: entries) ∧
        basisTransporterData[row.val + 1]? = some transporter ∧
        radixPackedNormalizedGramRowData[
          (transporter.getD 0 0).toNat]? = some [packedOrbit, packed] ∧
        stored = (row.val : Int) ∧
        entries.length = 424 ∧
        (transporter.getD 0 0).toNat < 26 ∧
        (transporter.getD 1 0).toNat < 64 ∧
        inverseSymmetry ((transporter.getD 1 0).toNat) < 64 ∧
        packedOrbit = ((transporter.getD 0 0).toNat : Int) ∧
        orbitRadixDenseGramEntriesCheck packed
          (pairWitnessPackedPermutationRows.getD
            (inverseSymmetry ((transporter.getD 1 0).toNat)) 0)
          0 entries = true := by
  have hcheck := orbitRadixDenseGramRows_valid row
  cases hdense : radixDenseReducedGramRowData[row.val]? with
  | none => simp [orbitRadixDenseGramRowCheck, hdense] at hcheck
  | some dense =>
      cases dense with
      | nil => simp [orbitRadixDenseGramRowCheck, hdense] at hcheck
      | cons stored entries =>
          cases htransport : basisTransporterData[row.val + 1]? with
          | none =>
              simp [orbitRadixDenseGramRowCheck, hdense, htransport] at hcheck
          | some transporter =>
              unfold orbitRadixDenseGramRowCheck at hcheck
              rw [hdense, htransport] at hcheck
              let orbit := (transporter.getD 0 0).toNat
              let symmetry := (transporter.getD 1 0).toNat
              let inverse := inverseSymmetry symmetry
              change
                (match radixPackedNormalizedGramRowData[orbit]? with
                  | some [packedOrbit, packed] =>
                      decide (stored = (row.val : Int)) &&
                        decide (entries.length = 424) &&
                        decide (orbit < 26) &&
                        decide (symmetry < 64) &&
                        decide (inverse < 64) &&
                        decide (packedOrbit = (orbit : Int)) &&
                        orbitRadixDenseGramEntriesCheck packed
                          (pairWitnessPackedPermutationRows.getD inverse 0)
                          0 entries
                  | _ => false) = true at hcheck
              cases hpacked : radixPackedNormalizedGramRowData[orbit]? with
              | none => simp [hpacked] at hcheck
              | some packedRow =>
                  cases packedRow with
                  | nil => simp [hpacked] at hcheck
                  | cons packedOrbit tail =>
                      cases tail with
                      | nil => simp [hpacked] at hcheck
                      | cons packed extra =>
                          cases extra with
                          | cons _ _ => simp [hpacked] at hcheck
                          | nil =>
                              simp only [hpacked, Bool.and_eq_true,
                                decide_eq_true_eq, and_assoc] at hcheck
                              refine ⟨stored, entries, transporter,
                                packedOrbit, packed, rfl, rfl, ?_⟩
                              change
                                radixPackedNormalizedGramRowData[orbit]? =
                                    some [packedOrbit, packed] ∧
                                  stored = (row.val : Int) ∧
                                  entries.length = 424 ∧
                                  orbit < 26 ∧ symmetry < 64 ∧ inverse < 64 ∧
                                  packedOrbit = (orbit : Int) ∧
                                  orbitRadixDenseGramEntriesCheck packed
                                    (pairWitnessPackedPermutationRows.getD
                                      inverse 0) 0 entries = true
                              exact ⟨hpacked, hcheck⟩

end ConnesRigidity.AffineSymplecticOrbitCertificate
