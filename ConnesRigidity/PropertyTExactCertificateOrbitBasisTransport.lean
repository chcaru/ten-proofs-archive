
import ConnesRigidity.PropertyTExactCertificateOrbitBasis

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix

def rawRowEq (x y : Array Int) : Bool :=
  (List.range 20).all fun i => decide (x.getD i 0 = y.getD i 0)

theorem rawRowEq_getD {x y : Array Int}
    (h : rawRowEq x y = true) {i : Nat} (hi : i < 20) :
    x.getD i 0 = y.getD i 0 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp h i (List.mem_range.mpr hi))

def coordinateIndex (i : Fin 4) : SymplecticIndex :=
  (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)).symm i

@[simp] theorem certificateIndex_coordinateIndex (i : Fin 4) :
    certificateIndex (coordinateIndex i) = i := by
  exact Equiv.apply_symm_apply _ i

def rawProductMatrixCoordinate (x y : Array Int) (i j : Nat) : Int :=
  matrixCoordinate x i 0 * matrixCoordinate y 0 j +
    matrixCoordinate x i 1 * matrixCoordinate y 1 j +
    matrixCoordinate x i 2 * matrixCoordinate y 2 j +
    matrixCoordinate x i 3 * matrixCoordinate y 3 j

def rawProductVectorCoordinate (x y : Array Int) (i : Nat) : Int :=
  vectorCoordinate x i +
    matrixCoordinate x i 0 * vectorCoordinate y 0 +
    matrixCoordinate x i 1 * vectorCoordinate y 1 +
    matrixCoordinate x i 2 * vectorCoordinate y 2 +
    matrixCoordinate x i 3 * vectorCoordinate y 3

def rawProductCheck (x y z : Array Int) : Bool :=
  (List.range 4).all fun i =>
    decide (vectorCoordinate z i = rawProductVectorCoordinate x y i) &&
      (List.range 4).all fun j =>
        decide (matrixCoordinate z i j = rawProductMatrixCoordinate x y i j)

theorem rawProductCheck_matrix {x y z : Array Int}
    (h : rawProductCheck x y z = true) (i j : Fin 4) :
    matrixCoordinate z i.val j.val =
      rawProductMatrixCoordinate x y i.val j.val := by
  have hi := List.all_eq_true.mp h i.val
    (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true] at hi
  have hij := hi.2
  exact of_decide_eq_true
    (List.all_eq_true.mp hij j.val (List.mem_range.mpr j.isLt))

theorem rawProductCheck_vector {x y z : Array Int}
    (h : rawProductCheck x y z = true) (i : Fin 4) :
    vectorCoordinate z i.val = rawProductVectorCoordinate x y i.val := by
  have hi := List.all_eq_true.mp h i.val
    (List.mem_range.mpr i.isLt)
  simp only [Bool.and_eq_true] at hi
  exact of_decide_eq_true hi.1

theorem rawProductCheck_sound {x y z : Array Int}
    (hx : isSymplecticRow x = true)
    (hy : isSymplecticRow y = true)
    (hz : isSymplecticRow z = true)
    (h : rawProductCheck x y z = true) :
    gammaZeroOfRow x * gammaZeroOfRow y = gammaZeroOfRow z := by
  change
    (show IntegralSymplecticCocycleInput.GammaZero from gammaZeroOfRow x) *
      (show IntegralSymplecticCocycleInput.GammaZero from gammaZeroOfRow y) =
        (show IntegralSymplecticCocycleInput.GammaZero from gammaZeroOfRow z)
  apply CocycleExtension.ext
  · funext i
    simp only [CocycleExtension.mul_fst, gammaZeroOfRow, hx, hy, hz,
      ↓reduceDIte, NormalizedAddCocycle.zero_apply, add_zero]
    change vectorOfRow x i + (matrixOfRow x).mulVec (vectorOfRow y) i =
      vectorOfRow z i
    have hi := rawProductCheck_vector h (certificateIndex i)
    rcases i with i | i <;> fin_cases i <;>
      norm_num [vectorOfRow, vectorCoordinate, matrixOfRow,
        matrixCoordinate, certificateIndex, Matrix.mulVec, dotProduct,
        rawProductVectorCoordinate] at hi ⊢ <;>
      linear_combination -hi
  · apply Subtype.ext
    ext i j
    simp only [CocycleExtension.mul_snd, gammaZeroOfRow, hx, hy, hz,
      ↓reduceDIte]
    change (matrixOfRow x * matrixOfRow y) i j = matrixOfRow z i j
    have hij := rawProductCheck_matrix h
      (certificateIndex i) (certificateIndex j)
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [matrixOfRow, matrixCoordinate, certificateIndex,
        Matrix.mul_apply, rawProductMatrixCoordinate] at hij ⊢ <;>
      linear_combination -hij

def signedActionMatrixCoordinate (symmetry row : Array Int)
    (i j : Nat) : Int :=
  symmetrySignCoordinate symmetry i * symmetrySignCoordinate symmetry j *
    matrixCoordinate row
      (symmetryPermutationCoordinate symmetry i)
      (symmetryPermutationCoordinate symmetry j)

def signedActionVectorCoordinate (symmetry row : Array Int)
    (i : Nat) : Int :=
  symmetrySignCoordinate symmetry i *
    vectorCoordinate row (symmetryPermutationCoordinate symmetry i)

def signedRowAction (symmetry row : Array Int) : Array Int :=
  Array.ofFn fun i : Fin 20 =>
    if i.val < 16 then
      signedActionMatrixCoordinate symmetry row (i.val / 4) (i.val % 4)
    else
      signedActionVectorCoordinate symmetry row (i.val - 16)

def signedTransportCheck (symmetry source target : Array Int) : Bool :=
  rawRowEq (signedRowAction symmetry source) target

theorem signedMatrixOfRow_mulVec_apply_of_coordinate_lt
    (symmetry : Array Int) (vector : IntegralLattice)
    (i : SymplecticIndex)
    (hsource :
      symmetryPermutationCoordinate symmetry (certificateIndex i).val < 4) :
    (signedMatrixOfRow symmetry).mulVec vector i =
      symmetrySignCoordinate symmetry (certificateIndex i).val *
        vector (coordinateIndex
          ⟨symmetryPermutationCoordinate symmetry (certificateIndex i).val,
            hsource⟩) := by
  classical
  let source : Fin 4 :=
    ⟨symmetryPermutationCoordinate symmetry (certificateIndex i).val,
      hsource⟩
  let selected : SymplecticIndex := coordinateIndex source
  have hselected : certificateIndex selected = source :=
    certificateIndex_coordinateIndex source
  change ∑ j, signedMatrixOfRow symmetry i j * vector j = _
  rw [Finset.sum_eq_single selected]
  · simp [signedMatrixOfRow, hselected, source, selected]
  · intro other _ hne
    have hcoordinate :
        (certificateIndex other).val ≠
          symmetryPermutationCoordinate symmetry (certificateIndex i).val := by
      intro heq
      apply hne
      apply (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)).injective
      apply Fin.ext
      change (certificateIndex other).val = (certificateIndex selected).val
      exact heq.trans (congrArg Fin.val hselected).symm
    simp [signedMatrixOfRow, hcoordinate]
  · simp

theorem signedMatrixOfRow_mul_matrix_apply_of_coordinate_lt
    (symmetry : Array Int)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (i j : SymplecticIndex)
    (hsource :
      symmetryPermutationCoordinate symmetry (certificateIndex i).val < 4) :
    (signedMatrixOfRow symmetry * matrix) i j =
      symmetrySignCoordinate symmetry (certificateIndex i).val *
        matrix
          (coordinateIndex
            ⟨symmetryPermutationCoordinate symmetry
              (certificateIndex i).val, hsource⟩) j := by
  classical
  let source : Fin 4 :=
    ⟨symmetryPermutationCoordinate symmetry (certificateIndex i).val,
      hsource⟩
  let selected : SymplecticIndex := coordinateIndex source
  have hselected : certificateIndex selected = source :=
    certificateIndex_coordinateIndex source
  rw [Matrix.mul_apply, Finset.sum_eq_single selected]
  · simp [signedMatrixOfRow, hselected, source, selected]
  · intro other _ hne
    have hcoordinate :
        (certificateIndex other).val ≠
          symmetryPermutationCoordinate symmetry (certificateIndex i).val := by
      intro heq
      apply hne
      apply (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)).injective
      apply Fin.ext
      change (certificateIndex other).val = (certificateIndex selected).val
      exact heq.trans (congrArg Fin.val hselected).symm
    simp [signedMatrixOfRow, hcoordinate]
  · simp

theorem signedMatrixOfRow_conjugate_apply_of_coordinate_lt
    (symmetry : Array Int)
    (matrix : Matrix SymplecticIndex SymplecticIndex Int)
    (i j : SymplecticIndex)
    (hi :
      symmetryPermutationCoordinate symmetry (certificateIndex i).val < 4)
    (hj :
      symmetryPermutationCoordinate symmetry (certificateIndex j).val < 4) :
    (signedMatrixOfRow symmetry * matrix *
        (signedMatrixOfRow symmetry).transpose) i j =
      symmetrySignCoordinate symmetry (certificateIndex i).val *
        symmetrySignCoordinate symmetry (certificateIndex j).val *
        matrix
          (coordinateIndex
            ⟨symmetryPermutationCoordinate symmetry
              (certificateIndex i).val, hi⟩)
          (coordinateIndex
            ⟨symmetryPermutationCoordinate symmetry
              (certificateIndex j).val, hj⟩) := by
  classical
  let source : Fin 4 :=
    ⟨symmetryPermutationCoordinate symmetry (certificateIndex j).val, hj⟩
  let selected : SymplecticIndex := coordinateIndex source
  have hselected : certificateIndex selected = source :=
    certificateIndex_coordinateIndex source
  rw [Matrix.mul_apply, Finset.sum_eq_single selected]
  · rw [Matrix.transpose_apply]
    simp [signedMatrixOfRow, hselected, source, selected]
    rw [signedMatrixOfRow_mul_matrix_apply_of_coordinate_lt
      symmetry matrix i selected hi]
    ring
  · intro other _ hne
    have hcoordinate :
        (certificateIndex other).val ≠
          symmetryPermutationCoordinate symmetry (certificateIndex j).val := by
      intro heq
      apply hne
      apply (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)).injective
      apply Fin.ext
      change (certificateIndex other).val = (certificateIndex selected).val
      exact heq.trans (congrArg Fin.val hselected).symm
    simp [Matrix.transpose_apply, signedMatrixOfRow, hcoordinate]
  · simp

theorem rawRowEq_matrixOfRow {x y : Array Int}
    (h : rawRowEq x y = true) : matrixOfRow x = matrixOfRow y := by
  ext i j
  apply rawRowEq_getD h
  have hi := (certificateIndex i).isLt
  have hj := (certificateIndex j).isLt
  omega

theorem rawRowEq_vectorOfRow {x y : Array Int}
    (h : rawRowEq x y = true) : vectorOfRow x = vectorOfRow y := by
  funext i
  apply rawRowEq_getD h
  have hi := (certificateIndex i).isLt
  omega

theorem rawRowEq_isSymplecticRow {x y : Array Int}
    (h : rawRowEq x y = true) : isSymplecticRow x = isSymplecticRow y := by
  unfold isSymplecticRow
  rw [rawRowEq_matrixOfRow h]

theorem rawRowEq_gammaZeroOfRow {x y : Array Int}
    (h : rawRowEq x y = true) : gammaZeroOfRow x = gammaZeroOfRow y := by
  have hm := rawRowEq_matrixOfRow h
  have hv := rawRowEq_vectorOfRow h
  have hs := rawRowEq_isSymplecticRow h
  unfold gammaZeroOfRow
  split <;> split
  · apply CocycleExtension.ext
    · exact hv
    · apply Subtype.ext
      exact hm
  · rename_i hx hy
    exact (hy (hs ▸ hx)).elim
  · rename_i hx hy
    exact (hx (hs.symm ▸ hy)).elim
  · rfl

theorem rawRowEq_iff_gammaZeroOfRow
    {x y : Array Int}
    (hx : isSymplecticRow x = true)
    (hy : isSymplecticRow y = true) :
    rawRowEq x y = true ↔ gammaZeroOfRow x = gammaZeroOfRow y := by
  constructor
  · exact rawRowEq_gammaZeroOfRow
  · intro heq
    unfold rawRowEq
    apply List.all_eq_true.mpr
    intro index hindex
    apply decide_eq_true
    have hbound : index < 20 := List.mem_range.mp hindex
    by_cases hmatrix : index < 16
    · have hrow : index / 4 < 4 := by omega
      have hcolumn : index % 4 < 4 := Nat.mod_lt _ (by omega)
      have hmat := congrArg
        (fun g : constructedGammaZeroGroup =>
          (g.snd : Matrix SymplecticIndex SymplecticIndex Int)) heq
      rw [gammaZeroOfRow_snd_of_symplectic hx,
        gammaZeroOfRow_snd_of_symplectic hy] at hmat
      have hentry := congrFun
        (congrFun hmat (coordinateIndex ⟨index / 4, hrow⟩))
          (coordinateIndex ⟨index % 4, hcolumn⟩)
      have hcoordinate : 4 * (index / 4) + index % 4 = index := by
        omega
      simpa [matrixOfRow, matrixCoordinate, hcoordinate] using hentry
    · have hvector : index - 16 < 4 := by omega
      have hvec := congrArg
        (fun g : constructedGammaZeroGroup => g.fst) heq
      rw [gammaZeroOfRow_fst_of_symplectic hx,
        gammaZeroOfRow_fst_of_symplectic hy] at hvec
      have hentry := congrFun hvec
        (coordinateIndex ⟨index - 16, hvector⟩)
      have hcoordinate : 16 + (index - 16) = index := by omega
      simpa [vectorOfRow, vectorCoordinate, hcoordinate] using hentry

theorem symmetryPermutationCoordinate_lt
    {symmetry : Array Int} (h : isSignedNormalizerRow symmetry = true)
    (i : Fin 4) : symmetryPermutationCoordinate symmetry i.val < 4 := by
  by_contra hnot
  have hzero (j : SymplecticIndex) :
      signedMatrixOfRow symmetry (coordinateIndex i) j = 0 := by
    simp [signedMatrixOfRow, certificateIndex_coordinateIndex,
      show (certificateIndex j).val ≠
        symmetryPermutationCoordinate symmetry i.val by
        have hj := (certificateIndex j).isLt
        omega]
  have horthogonal := (signedNormalizerOfRow symmetry).orthogonal
  rw [signedNormalizerOfRow_matrix_of_check h] at horthogonal
  have hdiagonal := congrFun (congrFun horthogonal (coordinateIndex i))
    (coordinateIndex i)
  simp [Matrix.mul_apply, hzero] at hdiagonal

theorem signedRowAction_matrixCoordinate
    (symmetry row : Array Int) (i j : Fin 4) :
    matrixCoordinate (signedRowAction symmetry row) i.val j.val =
      signedActionMatrixCoordinate symmetry row i.val j.val := by
  have hi := i.isLt
  have hj := j.isLt
  have hindex : 4 * i.val + j.val < 16 := by omega
  have hindex' : 4 * i.val + j.val < 20 := by omega
  have hdiv : (4 * i.val + j.val) / 4 = i.val := by omega
  have hmod : (4 * i.val + j.val) % 4 = j.val := by omega
  simp [matrixCoordinate, signedRowAction, Array.getD_eq_getD_getElem?,
    hindex, hindex', hdiv, hmod]

theorem signedRowAction_vectorCoordinate
    (symmetry row : Array Int) (i : Fin 4) :
    vectorCoordinate (signedRowAction symmetry row) i.val =
      signedActionVectorCoordinate symmetry row i.val := by
  have hi := i.isLt
  have hindex : 16 + i.val < 20 := by omega
  simp [vectorCoordinate, signedRowAction, Array.getD_eq_getD_getElem?,
    hindex]

theorem matrixOfRow_signedRowAction
    {symmetry row : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true) :
    matrixOfRow (signedRowAction symmetry row) =
      signedMatrixOfRow symmetry * matrixOfRow row *
        (signedMatrixOfRow symmetry).transpose := by
  ext i j
  change matrixCoordinate (signedRowAction symmetry row)
      (certificateIndex i).val (certificateIndex j).val = _
  rw [signedRowAction_matrixCoordinate]
  have hi := symmetryPermutationCoordinate_lt
    hsymmetry (certificateIndex i)
  have hj := symmetryPermutationCoordinate_lt
    hsymmetry (certificateIndex j)
  have hconjugate := signedMatrixOfRow_conjugate_apply_of_coordinate_lt
    symmetry (matrixOfRow row) i j hi hj
  simpa [signedActionMatrixCoordinate, matrixOfRow,
    certificateIndex, coordinateIndex] using hconjugate.symm

theorem vectorOfRow_signedRowAction
    {symmetry row : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true) :
    vectorOfRow (signedRowAction symmetry row) =
      (signedMatrixOfRow symmetry).mulVec (vectorOfRow row) := by
  funext i
  change vectorCoordinate (signedRowAction symmetry row)
      (certificateIndex i).val = _
  rw [signedRowAction_vectorCoordinate]
  have hi := symmetryPermutationCoordinate_lt
    hsymmetry (certificateIndex i)
  simpa [signedActionVectorCoordinate, vectorOfRow,
    certificateIndex, coordinateIndex] using
      (signedMatrixOfRow_mulVec_apply_of_coordinate_lt
        symmetry (vectorOfRow row) i hi).symm

theorem isSymplecticRow_signedRowAction
    {symmetry row : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true)
    (hrow : isSymplecticRow row = true) :
    isSymplecticRow (signedRowAction symmetry row) = true := by
  unfold isSymplecticRow
  apply decide_eq_true
  intro i j
  have hmember := ((signedNormalizerOfRow symmetry).symplecticConjugate
    (⟨matrixOfRow row, matrixOfRow_mem_symplectic hrow⟩ :
      IntegralSymplecticGroup)).property
  rw [SymplecticGroup.mem_iff] at hmember
  have hcoordinate := congrFun (congrFun hmember i) j
  rw [matrixOfRow_signedRowAction hsymmetry]
  simpa [SignedNormalizer.symplecticConjugate_val,
    signedNormalizerOfRow_matrix_of_check hsymmetry] using hcoordinate

theorem signedRowAction_sound
    {symmetry row : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true)
    (hrow : isSymplecticRow row = true) :
    gammaZeroOfRow (signedRowAction symmetry row) =
      (signedNormalizerOfRow symmetry).gammaZeroEquiv
        (gammaZeroOfRow row) := by
  have haction := isSymplecticRow_signedRowAction hsymmetry hrow
  apply CocycleExtension.ext
  · rw [gammaZeroOfRow_fst_of_symplectic haction,
      SignedNormalizer.gammaZeroEquiv_fst,
      gammaZeroOfRow_fst_of_symplectic hrow,
      signedNormalizerOfRow_matrix_of_check hsymmetry]
    exact vectorOfRow_signedRowAction hsymmetry
  · apply Subtype.ext
    simp only [SignedNormalizer.gammaZeroEquiv_snd,
      SignedNormalizer.symplecticConjugate_val,
      gammaZeroOfRow_snd_of_symplectic hrow,
      gammaZeroOfRow_snd_of_symplectic haction,
      signedNormalizerOfRow_matrix_of_check hsymmetry]
    exact matrixOfRow_signedRowAction hsymmetry

theorem signedTransportCheck_sound
    {symmetry source target : Array Int}
    (hsymmetry : isSignedNormalizerRow symmetry = true)
    (hsource : isSymplecticRow source = true)
    (hcheck : signedTransportCheck symmetry source target = true) :
    (signedNormalizerOfRow symmetry).gammaZeroEquiv
      (gammaZeroOfRow source) = gammaZeroOfRow target := by
  have haction := signedRowAction_sound hsymmetry hsource
  have hraw := rawRowEq_gammaZeroOfRow
    (show rawRowEq (signedRowAction symmetry source) target = true by
      simpa only [signedTransportCheck] using hcheck)
  exact haction.symm.trans hraw

end ConnesRigidity.AffineSymplecticOrbitCertificate
