
import ConnesRigidity.PropertyTExactCertificateOrbitIncidenceValidation
import ConnesRigidity.PropertyTExactCertificateOrbitPairWitnessValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option linter.style.setOption false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def orbitGramRepresentativePackedLookupRowCheck
    (index : Nat) (row : Array Int) : Bool :=
  let left := (orbitEntry row 0).toNat
  let right := (orbitEntry row 1).toNat
  let orbit := basisOrbit left
  let second := normalizedPairRight left right
  decide (orbit < 26) && decide (second < 425) &&
    decide (pairWitnessPackedPairOrbitIndex orbit second = index)

def orbitGramRepresentativePackedLookupCheck :
    List (Array Int) → Nat → Bool
  | [], _ => true
  | row :: rows, index =>
      orbitGramRepresentativePackedLookupRowCheck index row &&
        orbitGramRepresentativePackedLookupCheck rows (index + 1)

theorem orbitGramRepresentativePackedLookupCheck_valid :
    orbitGramRepresentativePackedLookupCheck gramOrbitData.toList 0 = true := by
  decide +kernel

theorem orbitGramRepresentativePackedLookupCheck_get
    (rows : List (Array Int)) (start index : Nat)
    (hindex : index < rows.length)
    (hcheck : orbitGramRepresentativePackedLookupCheck rows start = true) :
    orbitGramRepresentativePackedLookupRowCheck (start + index) rows[index] =
      true := by
  induction rows generalizing start index with
  | nil => simp at hindex
  | cons row rows ih =>
      simp only [orbitGramRepresentativePackedLookupCheck,
        Bool.and_eq_true] at hcheck
      cases index with
      | zero => simpa using hcheck.1
      | succ index =>
          have hindex' : index < rows.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2

theorem orbitGramRepresentativePairOrbit_valid
    (index : Nat) (hindex : index < gramOrbitData.size) :
    pairOrbit
      (orbitEntry gramOrbitData[index] 0).toNat
      (orbitEntry gramOrbitData[index] 1).toNat = index := by
  have hlookup := orbitGramRepresentativePackedLookupCheck_get
    gramOrbitData.toList 0 index
      (by simpa using hindex)
      orbitGramRepresentativePackedLookupCheck_valid
  simp only [Nat.zero_add, Array.getElem_toList] at hlookup
  simp only [orbitGramRepresentativePackedLookupRowCheck,
    Bool.and_eq_true, decide_eq_true_eq] at hlookup
  obtain ⟨⟨horbit, hsecond⟩, hvalue⟩ := hlookup
  have horbit' :
      basisOrbit (orbitEntry gramOrbitData[index] 0).toNat <
        pairOrbitIndexData.size := by
    simpa [pairWitnessDataSizes_valid.2.2.2.2.2.1] using horbit
  have hentry := pairWitnessPackedPairOrbitIndex_eq_dataEntry
    (basisOrbit (orbitEntry gramOrbitData[index] 0).toNat)
    (normalizedPairRight
      (orbitEntry gramOrbitData[index] 0).toNat
      (orbitEntry gramOrbitData[index] 1).toNat)
    horbit' hsecond
  unfold pairOrbit
  rw [← hentry]
  simpa using hvalue

theorem orbitGramRepresentativeCheck_valid :
    orbitGramRepresentativeCheck = true := by
  apply (orbitListRangeAll_iff orbitGramRepresentativeRowCheck
    gramOrbitData.size).mpr
  intro index hindex
  have hrow : gramOrbitData[index]? = some gramOrbitData[index] :=
    Array.getElem?_eq_getElem hindex
  have hfields := orbitGramRepresentativeFields_valid index hindex
  have hpair := orbitGramRepresentativePairOrbit_valid index hindex
  simp only [orbitGramRepresentativeRowCheck, hrow, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq]
  rcases hfields with
    ⟨hwidth, hleft, hright, hcoefficient, hincidence,
      htransport, hinversion, hsize⟩
  simp only [and_assoc]
  exact ⟨hwidth, hleft.1, hleft.2, hright.1, hright.2,
    hcoefficient.1, hcoefficient.2, hincidence,
    htransport.1, htransport.2, hinversion, hsize, hpair⟩

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
