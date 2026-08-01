


import ConnesRigidity.PropertyTExactCertificateOrbitCheckers
import ConnesRigidity.PropertyTExactCertificateOrbitIncidencePackedData










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


theorem gramOrbitData_size : gramOrbitData.size = 2256 := by
  decide +kernel


theorem coefficientRepresentativeData_size :
    coefficientRepresentativeData.size = 995 := by
  decide +kernel


theorem orbitGramOrbitSizeTotalCheck_valid :
    orbitGramOrbitSizeTotalCheck = true := by
  decide +kernel


def packedCoefficientOrbitSizes : Nat :=
  27328077310971983955369070251505087848867088664517718967345549747399754343065838214872786632183170340873258646570136217814275651450468947738080765691935078348282233017048841654006091306530272954263030336801019390634409914016479269728142749833528712261366693655742294666341408420378598251297527622680183902112647990795772451756099143666123756299815763447684164995968501458666651089217379604435453044327583173500883987190316948233896052902057533357413487411431143973498367194230587943158853575974596186455972284268717554676795294543424998135782336263714342726617359694613788980309333625608361206971892354012821564248335343080864479188777449573363570848899716067105891072470687620965583754598798712781793903071042261086430799305889558104679015703781936714846278241352128912812024131953121676584308983511632428736372119244091387803827515138782178132719354708115948027297658188063908820725389465164035800


def packedCoefficientOrbitSize (index : Nat) : Int :=
  (2 ^ ((packedCoefficientOrbitSizes >>> (3 * index)) % 8) : Nat)


def packedCoefficientOrbitSizesStreamingCheck :
    List (Array Int) → Nat → Bool
  | [], _ => true
  | row :: rows, index =>
      decide (row.size = 1) &&
        decide (orbitEntry row 0 = packedCoefficientOrbitSize index) &&
        packedCoefficientOrbitSizesStreamingCheck rows (index + 1)


theorem packedCoefficientOrbitSizesStreamingCheck_valid :
    packedCoefficientOrbitSizesStreamingCheck
      coefficientOrbitSizeData.toList 0 = true := by
  decide +kernel


theorem packedCoefficientOrbitSizesStreamingCheck_get
    (rows : List (Array Int)) (start index : Nat)
    (hindex : index < rows.length)
    (hcheck : packedCoefficientOrbitSizesStreamingCheck rows start = true) :
    orbitEntry rows[index] 0 = packedCoefficientOrbitSize (start + index) := by
  induction rows generalizing start index with
  | nil => simp at hindex
  | cons row rows ih =>
      simp only [packedCoefficientOrbitSizesStreamingCheck,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      cases index with
      | zero => simpa using hcheck.1.2
      | succ index =>
          have hindex' : index < rows.length := by
            simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2


theorem packedCoefficientOrbitSize_eq_dataEntry (index : Nat)
    (hindex : index < coefficientOrbitSizeData.size) :
    packedCoefficientOrbitSize index =
      dataEntry coefficientOrbitSizeData index 0 := by
  have hentry := packedCoefficientOrbitSizesStreamingCheck_get
    coefficientOrbitSizeData.toList 0 index
    (by simpa using hindex)
    packedCoefficientOrbitSizesStreamingCheck_valid
  simpa [dataEntry, orbitEntry, Array.getElem?_eq_getElem hindex] using
    hentry.symm


def orbitGramIncidenceStreamingRowCheck (row : Array Int) : Bool :=
  let coefficientOrbit := orbitEntry row 2
  let incidence := orbitEntry row 3
  let coefficientOrbitSize :=
    packedCoefficientOrbitSize coefficientOrbit.toNat
  decide (row.size = gramOrbitRowWidth) &&
    orbitIndexCheck coefficientOrbit coefficientOrbitSizeData.size &&
    decide (0 < incidence) &&
    decide (0 < coefficientOrbitSize) &&
    decide (orbitEntry row 7 = incidence * coefficientOrbitSize)


def orbitGramIncidenceStreamingCheck : Bool :=
  gramOrbitData.toList.all orbitGramIncidenceStreamingRowCheck


theorem orbitGramIncidenceCheck_of_streaming
    (hcheck : orbitGramIncidenceStreamingCheck = true) :
    orbitGramIncidenceCheck = true := by
  unfold orbitGramIncidenceCheck
  rw [List.all_eq_true]
  intro index hindex
  have hindex' : index < gramOrbitData.size := by
    simpa only [List.mem_range] using hindex
  have hrow : gramOrbitData[index]? = some gramOrbitData[index] :=
    Array.getElem?_eq_getElem hindex'
  have hvalid := (List.all_eq_true.mp hcheck)
    gramOrbitData[index] (Array.getElem_mem_toList hindex')
  simp only [orbitGramIncidenceStreamingRowCheck,
    Bool.and_eq_true, decide_eq_true_eq, orbitIndexCheck] at hvalid
  have hsizeIndex : (orbitEntry gramOrbitData[index] 2).toNat <
      coefficientOrbitSizeData.size := by
    exact (Int.toNat_lt hvalid.1.1.1.2.1).mpr hvalid.1.1.1.2.2
  rw [packedCoefficientOrbitSize_eq_dataEntry _ hsizeIndex] at hvalid
  simpa only [orbitGramIncidenceRowCheck, hrow, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq] using hvalid


theorem orbitGramIncidenceCheck_valid : orbitGramIncidenceCheck = true := by
  apply orbitGramIncidenceCheck_of_streaming
  decide +kernel


def orbitGramRepresentativeFieldsStreamingRowCheck
    (row : Array Int) : Bool :=
  let left := orbitEntry row 0
  let right := orbitEntry row 1
  decide (row.size = gramOrbitRowWidth) &&
    orbitIndexCheck left basisData.size &&
    orbitIndexCheck right basisData.size &&
    orbitIndexCheck (orbitEntry row 2) coefficientRepresentativeData.size &&
    decide (0 ≤ orbitEntry row 3) &&
    orbitIndexCheck (orbitEntry row 5) symmetryData.size &&
    decide (orbitEntry row 6 = 0 ∨ orbitEntry row 6 = 1) &&
    decide (0 < orbitEntry row 7)


theorem orbitGramRepresentativeFieldsStreamingCheck_valid :
    gramOrbitData.toList.all orbitGramRepresentativeFieldsStreamingRowCheck =
      true := by
  decide +kernel


theorem orbitGramRepresentativeFields_valid (index : Nat)
    (hindex : index < gramOrbitData.size) :
    let row := gramOrbitData[index]'hindex
    row.size = gramOrbitRowWidth ∧
      (0 ≤ orbitEntry row 0 ∧ orbitEntry row 0 < (basisData.size : Int)) ∧
      (0 ≤ orbitEntry row 1 ∧ orbitEntry row 1 < (basisData.size : Int)) ∧
      (0 ≤ orbitEntry row 2 ∧
        orbitEntry row 2 < (coefficientRepresentativeData.size : Int)) ∧
      0 ≤ orbitEntry row 3 ∧
      (0 ≤ orbitEntry row 5 ∧ orbitEntry row 5 < (symmetryData.size : Int)) ∧
      (orbitEntry row 6 = 0 ∨ orbitEntry row 6 = 1) ∧
      0 < orbitEntry row 7 := by
  have hrow := (List.all_eq_true.mp
    orbitGramRepresentativeFieldsStreamingCheck_valid)
      gramOrbitData[index] (Array.getElem_mem_toList hindex)
  simpa only [orbitGramRepresentativeFieldsStreamingRowCheck,
    orbitIndexCheck, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] using hrow


def orbitPackedNatEntry (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) % (2 ^ width)


def orbitPackedIntEntry (packed width index : Nat) : Int :=
  let value := orbitPackedNatEntry packed width index
  if value % 2 = 0 then (value / 2 : Nat)
  else -(((value + 1) / 2 : Nat) : Int)


def orbitPackedGramColumnsCheck : List (Array Int) → Nat → Bool
  | [], _ => true
  | row :: rows, index =>
      decide (orbitEntry row 2 =
        (orbitPackedNatEntry packedGramCoefficientOrbits 10 index : Nat)) &&
      decide (orbitEntry row 3 =
        (orbitPackedNatEntry packedGramIncidences 6 index : Nat)) &&
      decide (orbitEntry row 4 =
        orbitPackedIntEntry packedGramCoefficients 55 index) &&
      orbitPackedGramColumnsCheck rows (index + 1)


def orbitPackedWitnessColumnCheck
    (packed width : Nat) (hasSentinel : Bool) :
    List (Array Int) → Nat → Bool
  | [], _ => true
  | row :: rows, index =>
      decide (row.size = 1) &&
      decide (orbitEntry row 0 =
        (orbitPackedNatEntry packed width index : Int) -
          if hasSentinel then 1 else 0) &&
      orbitPackedWitnessColumnCheck packed width hasSentinel
        rows (index + 1)


def orbitPackedEquationColumnsCheck : List (Array Int) → Nat → Bool
  | [], _ => true
  | row :: rows, index =>
      decide (orbitEntry row 0 =
        (orbitPackedNatEntry packedEquationCoefficientOrbits 10 index : Nat)) &&
      decide (orbitEntry row 1 =
        (orbitPackedNatEntry packedEquationTermStarts 11 index : Nat)) &&
      decide (orbitEntry row 2 =
        (orbitPackedNatEntry packedEquationTermCounts 5 index : Nat)) &&
      decide (orbitEntry row 3 =
        orbitPackedIntEntry packedEquationTargets 57 index) &&
      orbitPackedEquationColumnsCheck rows (index + 1)


theorem orbitPackedIncidenceColumns_valid :
    orbitPackedGramColumnsCheck gramOrbitData.toList 0 = true ∧
    orbitPackedWitnessColumnCheck packedGramTermIndices 11 true
      gramOrbitTermIndexData.toList 0 = true ∧
    orbitPackedWitnessColumnCheck packedTermGramOrbits 12 false
      coefficientTermGramOrbitIndexData.toList 0 = true ∧
    orbitPackedWitnessColumnCheck packedCoefficientEquationIndices 10 true
      coefficientOrbitEquationIndexData.toList 0 = true ∧
    orbitPackedEquationColumnsCheck coefficientEquationData.toList 0 = true := by
  decide +kernel


theorem orbitPackedWitnessColumnCheck_get
    (packed width : Nat) (hasSentinel : Bool)
    (rows : List (Array Int)) (start index : Nat)
    (hindex : index < rows.length)
    (hcheck : orbitPackedWitnessColumnCheck
      packed width hasSentinel rows start = true) :
    orbitEntry rows[index] 0 =
      (orbitPackedNatEntry packed width (start + index) : Int) -
        if hasSentinel then 1 else 0 := by
  induction rows generalizing start index with
  | nil => simp at hindex
  | cons row rows ih =>
      simp only [orbitPackedWitnessColumnCheck, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      cases index with
      | zero => simpa using hcheck.1.2
      | succ index =>
          have hindex' : index < rows.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2


theorem orbitPackedGramColumnsCheck_get
    (rows : List (Array Int)) (start index : Nat)
    (hindex : index < rows.length)
    (hcheck : orbitPackedGramColumnsCheck rows start = true) :
    orbitEntry rows[index] 2 =
      (orbitPackedNatEntry packedGramCoefficientOrbits 10
        (start + index) : Nat) ∧
    orbitEntry rows[index] 3 =
      (orbitPackedNatEntry packedGramIncidences 6 (start + index) : Nat) ∧
    orbitEntry rows[index] 4 =
      orbitPackedIntEntry packedGramCoefficients 55 (start + index) := by
  induction rows generalizing start index with
  | nil => simp at hindex
  | cons row rows ih =>
      simp only [orbitPackedGramColumnsCheck, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      cases index with
      | zero =>
          exact ⟨hcheck.1.1.1, hcheck.1.1.2, hcheck.1.2⟩
      | succ index =>
          have hindex' : index < rows.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2


theorem orbitPackedEquationColumnsCheck_get
    (rows : List (Array Int)) (start index : Nat)
    (hindex : index < rows.length)
    (hcheck : orbitPackedEquationColumnsCheck rows start = true) :
    orbitEntry rows[index] 0 =
      (orbitPackedNatEntry packedEquationCoefficientOrbits 10
        (start + index) : Nat) ∧
    orbitEntry rows[index] 1 =
      (orbitPackedNatEntry packedEquationTermStarts 11
        (start + index) : Nat) ∧
    orbitEntry rows[index] 2 =
      (orbitPackedNatEntry packedEquationTermCounts 5
        (start + index) : Nat) ∧
    orbitEntry rows[index] 3 =
      orbitPackedIntEntry packedEquationTargets 57 (start + index) := by
  induction rows generalizing start index with
  | nil => simp at hindex
  | cons row rows ih =>
      simp only [orbitPackedEquationColumnsCheck, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      cases index with
      | zero =>
          exact ⟨hcheck.1.1.1.1, hcheck.1.1.1.2,
            hcheck.1.1.2, hcheck.1.2⟩
      | succ index =>
          have hindex' : index < rows.length := by simpa using hindex
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) index hindex' hcheck.2


theorem orbitPackedGramColumns_eq_dataEntry (index : Nat)
    (hindex : index < gramOrbitData.size) :
    dataEntry gramOrbitData index 2 =
        (orbitPackedNatEntry packedGramCoefficientOrbits 10 index : Nat) ∧
      dataEntry gramOrbitData index 3 =
        (orbitPackedNatEntry packedGramIncidences 6 index : Nat) ∧
      dataEntry gramOrbitData index 4 =
        orbitPackedIntEntry packedGramCoefficients 55 index := by
  have hentry := orbitPackedGramColumnsCheck_get
    gramOrbitData.toList 0 index (by simpa using hindex)
    orbitPackedIncidenceColumns_valid.1
  simpa [dataEntry, orbitEntry, Array.getElem?_eq_getElem hindex] using hentry


theorem orbitPackedEquationColumns_eq_dataEntry (index : Nat)
    (hindex : index < coefficientEquationData.size) :
    dataEntry coefficientEquationData index 0 =
        (orbitPackedNatEntry packedEquationCoefficientOrbits 10 index : Nat) ∧
      dataEntry coefficientEquationData index 1 =
        (orbitPackedNatEntry packedEquationTermStarts 11 index : Nat) ∧
      dataEntry coefficientEquationData index 2 =
        (orbitPackedNatEntry packedEquationTermCounts 5 index : Nat) ∧
      dataEntry coefficientEquationData index 3 =
        orbitPackedIntEntry packedEquationTargets 57 index := by
  have hentry := orbitPackedEquationColumnsCheck_get
    coefficientEquationData.toList 0 index (by simpa using hindex)
    orbitPackedIncidenceColumns_valid.2.2.2.2
  simpa [dataEntry, orbitEntry, Array.getElem?_eq_getElem hindex] using hentry


theorem orbitPackedTermGramOrbit_eq_dataEntry (index : Nat)
    (hindex : index < coefficientTermGramOrbitIndexData.size) :
    (orbitPackedNatEntry packedTermGramOrbits 12 index : Int) =
      dataEntry coefficientTermGramOrbitIndexData index 0 := by
  have hentry := orbitPackedWitnessColumnCheck_get
    packedTermGramOrbits 12 false
    coefficientTermGramOrbitIndexData.toList 0 index
    (by simpa using hindex) orbitPackedIncidenceColumns_valid.2.2.1
  simpa [dataEntry, orbitEntry, Array.getElem?_eq_getElem hindex] using
    hentry.symm


theorem orbitPackedGramTermIndex_eq_dataEntry (index : Nat)
    (hindex : index < gramOrbitTermIndexData.size) :
    (orbitPackedNatEntry packedGramTermIndices 11 index : Int) - 1 =
      dataEntry gramOrbitTermIndexData index 0 := by
  have hentry := orbitPackedWitnessColumnCheck_get
    packedGramTermIndices 11 true gramOrbitTermIndexData.toList 0 index
    (by simpa using hindex) orbitPackedIncidenceColumns_valid.2.1
  simpa [dataEntry, orbitEntry, Array.getElem?_eq_getElem hindex] using
    hentry.symm


theorem orbitPackedCoefficientEquationIndex_eq_dataEntry (index : Nat)
    (hindex : index < coefficientOrbitEquationIndexData.size) :
    (orbitPackedNatEntry packedCoefficientEquationIndices 10 index : Int) - 1 =
      dataEntry coefficientOrbitEquationIndexData index 0 := by
  have hentry := orbitPackedWitnessColumnCheck_get
    packedCoefficientEquationIndices 10 true
    coefficientOrbitEquationIndexData.toList 0 index
    (by simpa using hindex) orbitPackedIncidenceColumns_valid.2.2.2.1
  simpa [dataEntry, orbitEntry, Array.getElem?_eq_getElem hindex] using
    hentry.symm


def orbitTermGramStreamingRowCheck
    (term witness : Array Int) (index : Nat) : Bool :=
  let orbit := orbitEntry witness 0
  let equation :=
    (orbitPackedNatEntry packedCoefficientEquationIndices 10
      (orbitEntry term 0).toNat : Int) - 1
  orbitIndexCheck orbit gramOrbitData.size &&
    decide (term.size = coefficientTermRowWidth) &&
    decide (witness.size = 1) &&
    decide (orbitEntry term 0 =
      (orbitPackedNatEntry packedGramCoefficientOrbits 10 orbit.toNat : Nat)) &&
    decide (orbitEntry term 1 =
      (orbitPackedNatEntry packedGramIncidences 6 orbit.toNat : Nat)) &&
    decide (orbitEntry term 2 =
      orbitPackedIntEntry packedGramCoefficients 55 orbit.toNat) &&
    decide (orbitEntry term 2 ≠ 0) &&
    decide
      ((orbitPackedNatEntry packedGramTermIndices 11 orbit.toNat : Int) =
        (index + 1 : Nat)) &&
    orbitIndexCheck equation coefficientEquationData.size &&
    decide (orbitEntry term 0 =
      (orbitPackedNatEntry packedEquationCoefficientOrbits 10 equation.toNat : Nat)) &&
    decide
      (orbitPackedNatEntry packedEquationTermStarts 11 equation.toNat ≤ index) &&
    decide
      (index < orbitPackedNatEntry packedEquationTermStarts 11 equation.toNat +
        orbitPackedNatEntry packedEquationTermCounts 5 equation.toNat)


def orbitTermGramStreamingCheck :
    List (Array Int) → List (Array Int) → Nat → Bool
  | [], [], _ => true
  | term :: terms, witness :: witnesses, index =>
      orbitTermGramStreamingRowCheck term witness index &&
        orbitTermGramStreamingCheck terms witnesses (index + 1)
  | _, _, _ => false


theorem orbitTermGramStreamingCheck_valid :
    orbitTermGramStreamingCheck coefficientTermData.toList
      coefficientTermGramOrbitIndexData.toList 0 = true := by
  decide +kernel


theorem orbitTermGramStreamingCheck_get
    (terms witnesses : List (Array Int)) (start index : Nat)
    (hindex : index < terms.length) (hwitness : index < witnesses.length)
    (hcheck : orbitTermGramStreamingCheck terms witnesses start = true) :
    orbitTermGramStreamingRowCheck terms[index] witnesses[index]
      (start + index) = true := by
  induction terms generalizing witnesses start index with
  | nil => simp at hindex
  | cons term terms ih =>
      cases witnesses with
      | nil => simp at hwitness
      | cons witness witnesses =>
          simp only [orbitTermGramStreamingCheck,
            Bool.and_eq_true] at hcheck
          cases index with
          | zero => simpa using hcheck.1
          | succ index =>
              have hindex' : index < terms.length := by simpa using hindex
              have hwitness' : index < witnesses.length := by simpa using hwitness
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih witnesses (start + 1) index hindex' hwitness' hcheck.2


theorem coefficientTermGramOrbitIndexData_size :
    coefficientTermGramOrbitIndexData.size = coefficientTermData.size := by
  decide +kernel


theorem orbitTermGramStreamingRow_valid
    (index : Nat) (hindex : index < coefficientTermData.size) :
    orbitTermGramStreamingRowCheck
      coefficientTermData[index]
      (coefficientTermGramOrbitIndexData[index]'(by
        rw [coefficientTermGramOrbitIndexData_size]
        exact hindex)) index = true := by
  have hwitness : index < coefficientTermGramOrbitIndexData.size := by
    rwa [coefficientTermGramOrbitIndexData_size]
  have hrow := orbitTermGramStreamingCheck_get
    coefficientTermData.toList coefficientTermGramOrbitIndexData.toList
    0 index (by simpa using hindex) (by simpa using hwitness)
    orbitTermGramStreamingCheck_valid
  simpa using hrow


theorem orbitCoefficientTermGramOrbitRowCheck_valid
    (index : Nat) (hindex : index < coefficientTermData.size) :
    orbitCoefficientTermGramOrbitRowCheck index = true := by
  have hwitnessIndex : index < coefficientTermGramOrbitIndexData.size := by
    rwa [coefficientTermGramOrbitIndexData_size]
  let term := coefficientTermData[index]'hindex
  let witness := coefficientTermGramOrbitIndexData[index]'hwitnessIndex
  have hterm : coefficientTermData[index]? = some term :=
    Array.getElem?_eq_getElem hindex
  have hwitness : coefficientTermGramOrbitIndexData[index]? = some witness :=
    Array.getElem?_eq_getElem hwitnessIndex
  have hstream := orbitTermGramStreamingRow_valid index hindex
  change orbitTermGramStreamingRowCheck term witness index = true at hstream
  simp only [orbitTermGramStreamingRowCheck, orbitIndexCheck,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hstream
  obtain ⟨horbitNonneg, horbitLt, htermWidth, hwitnessWidth,
    htermKeyPacked, htermIncidencePacked, htermValuePacked,
    htermNonzero, hreversePacked, hequationNonneg, hequationLt,
    htermEquationPacked, hstartPacked, hendPacked⟩ := hstream
  let orbit := orbitEntry witness 0
  have horbit : orbit.toNat < gramOrbitData.size :=
    (Int.toNat_lt horbitNonneg).mpr horbitLt
  have hgram := orbitPackedGramColumns_eq_dataEntry orbit.toNat horbit
  have hkey : (orbitEntry term 0).toNat <
      coefficientOrbitEquationIndexData.size := by
    have hkeyGram : orbitEntry term 0 =
        dataEntry gramOrbitData orbit.toNat 2 := by
      exact htermKeyPacked.trans hgram.1.symm
    have hrepresentative := orbitGramRepresentativeFields_valid orbit.toNat horbit
    have hkeyBound := hrepresentative.2.2.2.1.2
    have hkeyNonneg := hrepresentative.2.2.2.1.1
    rw [hkeyGram]
    have hsize : coefficientOrbitEquationIndexData.size =
        coefficientRepresentativeData.size := by decide +kernel
    rw [hsize]
    have hkeyBound' :
        dataEntry gramOrbitData orbit.toNat 2 <
          (coefficientRepresentativeData.size : Int) := by
      simpa [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?, horbit]
        using hkeyBound
    have hkeyNonneg' : 0 ≤ dataEntry gramOrbitData orbit.toNat 2 := by
      simpa [dataEntry, orbitEntry, Array.getD_eq_getD_getElem?, horbit]
        using hkeyNonneg
    exact (Int.toNat_lt hkeyNonneg').mpr hkeyBound'
  have hequationPacked :=
    orbitPackedCoefficientEquationIndex_eq_dataEntry
      (orbitEntry term 0).toNat hkey
  let equation := dataEntry coefficientOrbitEquationIndexData
    (orbitEntry term 0).toNat 0
  have hequationValue :
      equation =
        (orbitPackedNatEntry packedCoefficientEquationIndices 10
          (orbitEntry term 0).toNat : Int) - 1 := hequationPacked.symm
  have hequationNat :
      equation.toNat =
        ((orbitPackedNatEntry packedCoefficientEquationIndices 10
          (orbitEntry term 0).toNat : Int) - 1).toNat :=
    congrArg Int.toNat hequationValue
  rw [← hequationNat] at htermEquationPacked hstartPacked hendPacked
  have hequationIndex : equation.toNat < coefficientEquationData.size := by
    rw [hequationValue]
    exact (Int.toNat_lt hequationNonneg).mpr hequationLt
  have hequation := orbitPackedEquationColumns_eq_dataEntry
    equation.toNat hequationIndex
  have hreverse := orbitPackedGramTermIndex_eq_dataEntry orbit.toNat (by
    have hsize : gramOrbitTermIndexData.size = gramOrbitData.size := by
      decide +kernel
    rwa [hsize])
  simp only [orbitCoefficientTermGramOrbitRowCheck, hterm, hwitness,
    orbitIndexCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨htermWidth, hwitnessWidth, horbitNonneg, horbitLt, ?_, ?_, ?_,
    ?_, ?_, htermNonzero, ?_, ?_, ?_, ?_⟩
  · simpa [equation, hequationValue] using hequationNonneg
  · simpa [equation, hequationValue] using hequationLt
  · simpa [dataEntry, orbitEntry, orbit] using htermKeyPacked.trans hgram.1.symm
  · simpa [dataEntry, orbitEntry, orbit] using
      htermIncidencePacked.trans hgram.2.1.symm
  · simpa [dataEntry, orbitEntry, orbit] using
      htermValuePacked.trans hgram.2.2.symm
  · have hidentity := hequation.1.trans htermEquationPacked.symm
    simpa [dataEntry, orbitEntry, equation] using hidentity
  · have hstart :
        (dataEntry coefficientEquationData equation.toNat 1).toNat =
          orbitPackedNatEntry packedEquationTermStarts 11 equation.toNat := by
      simpa using congrArg Int.toNat hequation.2.1
    change (dataEntry coefficientEquationData equation.toNat 1).toNat ≤ index
    rw [hstart]
    exact hstartPacked
  · have hstart :
        (dataEntry coefficientEquationData equation.toNat 1).toNat =
          orbitPackedNatEntry packedEquationTermStarts 11 equation.toNat := by
      simpa using congrArg Int.toNat hequation.2.1
    have hcount :
        (dataEntry coefficientEquationData equation.toNat 2).toNat =
          orbitPackedNatEntry packedEquationTermCounts 5 equation.toNat := by
      simpa using congrArg Int.toNat hequation.2.2.1
    change index < (dataEntry coefficientEquationData equation.toNat 1).toNat +
      (dataEntry coefficientEquationData equation.toNat 2).toNat
    rw [hstart, hcount]
    exact hendPacked
  · rw [← hreverse]
    have hpacked :
        (orbitPackedNatEntry packedGramTermIndices 11 orbit.toNat : Int) =
          (index : Int) + 1 := by
      simpa [orbit] using hreversePacked
    omega


theorem orbitCoefficientTermGramOrbitCheck_valid :
    orbitCoefficientTermGramOrbitCheck = true := by
  simp only [orbitCoefficientTermGramOrbitCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  exact ⟨coefficientTermGramOrbitIndexData_size,
    orbitCoefficientTermGramOrbitRowCheck_valid⟩


def orbitIndexedZipStreamingCheck
    (check : Array Int → Array Int → Nat → Bool) :
    List (Array Int) → List (Array Int) → Nat → Bool
  | [], [], _ => true
  | first :: firsts, second :: seconds, index =>
      check first second index &&
        orbitIndexedZipStreamingCheck check firsts seconds (index + 1)
  | _, _, _ => false


theorem orbitIndexedZipStreamingCheck_get
    (check : Array Int → Array Int → Nat → Bool)
    (first second : List (Array Int)) (start index : Nat)
    (hfirst : index < first.length) (hsecond : index < second.length)
    (hcheck : orbitIndexedZipStreamingCheck check first second start = true) :
    check first[index] second[index] (start + index) = true := by
  induction first generalizing second start index with
  | nil => simp at hfirst
  | cons value values ih =>
      cases second with
      | nil => simp at hsecond
      | cons witness witnesses =>
          simp only [orbitIndexedZipStreamingCheck, Bool.and_eq_true] at hcheck
          cases index with
          | zero => simpa using hcheck.1
          | succ index =>
              have hfirst' : index < values.length := by simpa using hfirst
              have hsecond' : index < witnesses.length := by simpa using hsecond
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih witnesses (start + 1) index hfirst' hsecond' hcheck.2


def orbitGramTermInverseStreamingRowCheck
    (gram witness : Array Int) (index : Nat) : Bool :=
  let term := orbitEntry witness 0
  decide (witness.size = 1) &&
    if orbitEntry gram 4 = 0 then
      decide (term = -1)
    else
      orbitIndexCheck term coefficientTermData.size &&
        decide
          (orbitPackedNatEntry packedTermGramOrbits 12 term.toNat = index)


theorem orbitGramTermInverseStreamingCheck_valid :
    orbitIndexedZipStreamingCheck orbitGramTermInverseStreamingRowCheck
      gramOrbitData.toList gramOrbitTermIndexData.toList 0 = true := by
  decide +kernel


theorem gramOrbitTermIndexData_size :
    gramOrbitTermIndexData.size = gramOrbitData.size := by
  decide +kernel


theorem orbitGramTermIndexRowCheck_valid
    (index : Nat) (hindex : index < gramOrbitData.size) :
    orbitGramTermIndexRowCheck index = true := by
  have hwitnessIndex : index < gramOrbitTermIndexData.size := by
    rwa [gramOrbitTermIndexData_size]
  let gram := gramOrbitData[index]'hindex
  let witness := gramOrbitTermIndexData[index]'hwitnessIndex
  have hgram : gramOrbitData[index]? = some gram :=
    Array.getElem?_eq_getElem hindex
  have hwitness : gramOrbitTermIndexData[index]? = some witness :=
    Array.getElem?_eq_getElem hwitnessIndex
  have hstream' := orbitIndexedZipStreamingCheck_get
    orbitGramTermInverseStreamingRowCheck
    gramOrbitData.toList gramOrbitTermIndexData.toList 0 index
    (by simpa using hindex) (by simpa using hwitnessIndex)
    orbitGramTermInverseStreamingCheck_valid
  have hstream : orbitGramTermInverseStreamingRowCheck gram witness index =
      true := by simpa [gram, witness] using hstream'
  simp only [orbitGramTermInverseStreamingRowCheck, Bool.and_eq_true,
    decide_eq_true_eq] at hstream
  unfold orbitGramTermIndexRowCheck
  rw [hgram, hwitness]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hstream.1, ?_⟩
  split <;> rename_i hzero
  · simpa [hzero] using hstream.2
  · simp only [hzero, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq] at hstream ⊢
    refine ⟨hstream.2.1, ?_⟩
    have htermBounds := orbitIndexCheck_sound _ _ hstream.2.1
    have hterm : (orbitEntry witness 0).toNat <
        coefficientTermGramOrbitIndexData.size := by
      rw [coefficientTermGramOrbitIndexData_size]
      exact (Int.toNat_lt htermBounds.1).mpr htermBounds.2
    rw [← orbitPackedTermGramOrbit_eq_dataEntry _ hterm]
    exact_mod_cast hstream.2.2


theorem orbitGramTermIndexCheck_valid : orbitGramTermIndexCheck = true := by
  simp only [orbitGramTermIndexCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range]
  exact ⟨gramOrbitTermIndexData_size, orbitGramTermIndexRowCheck_valid⟩


def orbitCoefficientEquationInverseStreamingRowCheck
    (inverse target : Array Int) (index : Nat) : Bool :=
  let equation := orbitEntry inverse 0
  decide (inverse.size = 1) && decide (target.size = 1) &&
    if equation = -1 then
      decide (orbitEntry target 0 = 0)
    else
      orbitIndexCheck equation coefficientEquationData.size &&
        decide
          (orbitPackedNatEntry packedEquationCoefficientOrbits 10
            equation.toNat = index) &&
        decide
          (orbitPackedIntEntry packedEquationTargets 57 equation.toNat =
            orbitEntry target 0)


theorem orbitCoefficientEquationInverseStreamingCheck_valid :
    orbitIndexedZipStreamingCheck
      orbitCoefficientEquationInverseStreamingRowCheck
      coefficientOrbitEquationIndexData.toList coefficientTargetData.toList
      0 = true := by
  decide +kernel


theorem coefficientOrbitEquationIndexData_size :
    coefficientOrbitEquationIndexData.size =
      coefficientRepresentativeData.size := by
  decide +kernel


theorem coefficientTargetData_size :
    coefficientTargetData.size = coefficientRepresentativeData.size := by
  decide +kernel


theorem orbitCoefficientOrbitEquationRowCheck_valid
    (index : Nat) (hindex : index < coefficientRepresentativeData.size) :
    orbitCoefficientOrbitEquationRowCheck index = true := by
  have hinverseIndex : index < coefficientOrbitEquationIndexData.size := by
    rwa [coefficientOrbitEquationIndexData_size]
  have htargetIndex : index < coefficientTargetData.size := by
    rwa [coefficientTargetData_size]
  let inverse := coefficientOrbitEquationIndexData[index]'hinverseIndex
  let target := coefficientTargetData[index]'htargetIndex
  have hinverse : coefficientOrbitEquationIndexData[index]? = some inverse :=
    Array.getElem?_eq_getElem hinverseIndex
  have htarget : coefficientTargetData[index]? = some target :=
    Array.getElem?_eq_getElem htargetIndex
  have hstream' := orbitIndexedZipStreamingCheck_get
    orbitCoefficientEquationInverseStreamingRowCheck
    coefficientOrbitEquationIndexData.toList coefficientTargetData.toList
    0 index (by simpa using hinverseIndex) (by simpa using htargetIndex)
    orbitCoefficientEquationInverseStreamingCheck_valid
  have hstream : orbitCoefficientEquationInverseStreamingRowCheck
      inverse target index = true := by
    simpa [inverse, target] using hstream'
  simp only [orbitCoefficientEquationInverseStreamingRowCheck,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hstream
  unfold orbitCoefficientOrbitEquationRowCheck
  rw [hinverse, htarget]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hstream.1, hstream.2.1, ?_⟩
  split <;> rename_i hequation
  · simpa [hequation] using hstream.2.2
  · simp only [hequation, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq, and_assoc] at hstream ⊢
    have hbounds := orbitIndexCheck_sound _ _ hstream.2.2.1
    have hequationIndex : (orbitEntry inverse 0).toNat <
        coefficientEquationData.size :=
      (Int.toNat_lt hbounds.1).mpr hbounds.2
    have hfields := orbitPackedEquationColumns_eq_dataEntry
      (orbitEntry inverse 0).toNat hequationIndex
    refine ⟨hstream.2.2.1, ?_, ?_⟩
    · unfold coefficientEquationOrbit
      rw [hfields.1]
      exact_mod_cast hstream.2.2.2.1
    · unfold coefficientEquationTarget
      rw [hfields.2.2.2]
      exact hstream.2.2.2.2


theorem orbitCoefficientOrbitEquationCheck_valid :
    orbitCoefficientOrbitEquationCheck = true := by
  simp only [orbitCoefficientOrbitEquationCheck, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc]
  exact ⟨coefficientOrbitEquationIndexData_size,
    coefficientTargetData_size, orbitCoefficientOrbitEquationRowCheck_valid⟩

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
