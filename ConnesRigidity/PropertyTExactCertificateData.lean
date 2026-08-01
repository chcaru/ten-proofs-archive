
import ConnesRigidity.ArithmeticCocycle
import Lean
import ConnesRigidity.GroupRingCertificateAlgebra
import ConnesRigidity.PropertyTExactCertificateAllElementChunks
import ConnesRigidity.PropertyTExactCertificateFullGramRows
import ConnesRigidity.PropertyTExactCertificateProductIndexRows
import ConnesRigidity.PropertyTSumOfSquares
import Mathlib.Data.List.GetD
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry000
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry001
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry002
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry003
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry004
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry005
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry006
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry007
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry008
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry009
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry010
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry011
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry012
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry013
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry014
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry015
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry016
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry017
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry018
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry019
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry020
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry021
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry022
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry023
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry024
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry025
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry026
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry027
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry028
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry029
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry030
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry031
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry032
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry033
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry034
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry035
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry036
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry037
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry038
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry039
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry040
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry041
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry042

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

local instance cocycleExtensionDecidableEq
    {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [DecidableEq G] [DecidableEq A]
    {c : NormalizedAddCocycle G A} :
    DecidableEq (CocycleExtension c) :=
  fun x y =>
    decidable_of_iff (x.fst = y.fst ∧ x.snd = y.snd)
      ⟨fun h ↦ by cases x; cases y; simp_all,
       fun h ↦ ⟨congrArg CocycleExtension.fst h,
         congrArg CocycleExtension.snd h⟩⟩

private structure IntRowsParserState where
  rowsRev : List (List ℤ) := []
  rowRev : List ℤ := []
  magnitude : ℕ := 0
  negative : Bool := false

private def IntRowsParserState.pushValue
    (state : IntRowsParserState) : IntRowsParserState :=
  let value : ℤ :=
    if state.negative then -(state.magnitude : ℤ)
    else state.magnitude
  { state with
    rowRev := value :: state.rowRev
    magnitude := 0
    negative := false }

private def IntRowsParserState.finishRow
    (state : IntRowsParserState) : IntRowsParserState :=
  let state := state.pushValue
  { state with
    rowsRev := state.rowRev.reverse :: state.rowsRev
    rowRev := [] }

private def decimalDigit? (c : Char) : Option ℕ :=
  if c = '0' then some 0
  else if c = '1' then some 1
  else if c = '2' then some 2
  else if c = '3' then some 3
  else if c = '4' then some 4
  else if c = '5' then some 5
  else if c = '6' then some 6
  else if c = '7' then some 7
  else if c = '8' then some 8
  else if c = '9' then some 9
  else none

private def parseIntRowsStep
    (state : IntRowsParserState) (c : Char) : IntRowsParserState :=
  if c = '-' then
    { state with negative := true }
  else if c = ',' then
    state.pushValue
  else if c = '\n' then
    state.finishRow
  else
    match decimalDigit? c with
    | some digit =>
        { state with magnitude := 10 * state.magnitude + digit }
    | none => state

def parseIntRows (text : String) : List (List ℤ) :=
  (text.toList.foldl parseIntRowsStep {}).rowsRev.reverse

def parseIntRowsChunks (chunks : List String) : List (List ℤ) :=
  chunks.flatMap parseIntRows

def generatorData : List (List ℤ) :=
  [
    [1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, -1, 0, 1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, -1, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1]
  ]

@[irreducible] noncomputable def basisDataArray : Array (Array ℤ) :=
  ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry000.data

@[irreducible] noncomputable def basisData : List (List ℤ) :=
  basisDataArray.toList.map Array.toList

set_option maxHeartbeats 0 in

@[irreducible] noncomputable def factorData : List (List ℤ) :=
  List.flatten [
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry001.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry002.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry003.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry004.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry005.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry006.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry007.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry008.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry009.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry010.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry011.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry012.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry013.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry014.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry015.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry016.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry017.data]

set_option maxHeartbeats 0 in

@[irreducible] noncomputable def negativeEdgeData : List (List ℤ) :=
  List.flatten [
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry018.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry019.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry020.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry021.data]

set_option maxHeartbeats 0 in

@[irreducible] noncomputable def positiveEdgeData : List (List ℤ) :=
  List.flatten [
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry022.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry023.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry024.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry025.data]

@[irreducible] def diagonalWeightData : List ℤ :=
  (parseIntRows
    (include_str
      "Certificates"/"AffineSymplectic"/"diagonal_weights.txt")).headD []

@[irreducible] noncomputable def productIndexDataArray : Array (Array ℤ) :=
  productIndexDataRows

@[irreducible] noncomputable def productIndexData : List (List ℤ) :=
  productIndexDataArray.toList.map Array.toList

noncomputable abbrev fullGramData : List (List ℤ) :=
  coefficientFullGramData

def gramEncodingBase : ℤ := 100000000000000000000

def encodeGramRow (entries : List ℤ) : ℤ :=
  entries.foldr (fun entry result ↦ entry + gramEncodingBase * result) 0

set_option maxHeartbeats 0 in

@[irreducible] noncomputable def encodedFactorRowData : List (List ℤ) :=
  List.flatten [
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry026.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry027.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry028.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry029.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry030.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry031.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry032.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry033.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry034.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry035.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry036.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry037.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry038.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry039.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry040.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry041.data,
    ConnesRigidity.CertificateLiterals.PropertyTExactCertificateData.Entry042.data]

@[irreducible] noncomputable def encodedFactorRows : List ℤ :=
  encodedFactorRowData.map fun row ↦ row.headD 0

private structure RawAffineCoordinates where
  m00 : ℤ
  m01 : ℤ
  m02 : ℤ
  m03 : ℤ
  m10 : ℤ
  m11 : ℤ
  m12 : ℤ
  m13 : ℤ
  m20 : ℤ
  m21 : ℤ
  m22 : ℤ
  m23 : ℤ
  m30 : ℤ
  m31 : ℤ
  m32 : ℤ
  m33 : ℤ
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ

private def rawAffineCoordinatesListGetD
    (data : List ℤ) : RawAffineCoordinates where
  m00 := data.getD 0 0
  m01 := data.getD 1 0
  m02 := data.getD 2 0
  m03 := data.getD 3 0
  m10 := data.getD 4 0
  m11 := data.getD 5 0
  m12 := data.getD 6 0
  m13 := data.getD 7 0
  m20 := data.getD 8 0
  m21 := data.getD 9 0
  m22 := data.getD 10 0
  m23 := data.getD 11 0
  m30 := data.getD 12 0
  m31 := data.getD 13 0
  m32 := data.getD 14 0
  m33 := data.getD 15 0
  v0 := data.getD 16 0
  v1 := data.getD 17 0
  v2 := data.getD 18 0
  v3 := data.getD 19 0

private def rawAffineCoordinatesOfList
    (data : List ℤ) : RawAffineCoordinates :=
  match data with
  | m00 :: m01 :: m02 :: m03 ::
      m10 :: m11 :: m12 :: m13 ::
      m20 :: m21 :: m22 :: m23 ::
      m30 :: m31 :: m32 :: m33 ::
      v0 :: v1 :: v2 :: v3 :: _ =>
      { m00, m01, m02, m03
        m10, m11, m12, m13
        m20, m21, m22, m23
        m30, m31, m32, m33
        v0, v1, v2, v3 }
  | _ => rawAffineCoordinatesListGetD data

@[simp] private theorem rawAffineCoordinatesOfList_eq_getD
    (data : List ℤ) :
    rawAffineCoordinatesOfList data =
      rawAffineCoordinatesListGetD data := by
  rcases data with _ | ⟨m00, rest⟩
  · rfl
  rcases rest with _ | ⟨m01, rest⟩
  · rfl
  rcases rest with _ | ⟨m02, rest⟩
  · rfl
  rcases rest with _ | ⟨m03, rest⟩
  · rfl
  rcases rest with _ | ⟨m10, rest⟩
  · rfl
  rcases rest with _ | ⟨m11, rest⟩
  · rfl
  rcases rest with _ | ⟨m12, rest⟩
  · rfl
  rcases rest with _ | ⟨m13, rest⟩
  · rfl
  rcases rest with _ | ⟨m20, rest⟩
  · rfl
  rcases rest with _ | ⟨m21, rest⟩
  · rfl
  rcases rest with _ | ⟨m22, rest⟩
  · rfl
  rcases rest with _ | ⟨m23, rest⟩
  · rfl
  rcases rest with _ | ⟨m30, rest⟩
  · rfl
  rcases rest with _ | ⟨m31, rest⟩
  · rfl
  rcases rest with _ | ⟨m32, rest⟩
  · rfl
  rcases rest with _ | ⟨m33, rest⟩
  · rfl
  rcases rest with _ | ⟨v0, rest⟩
  · rfl
  rcases rest with _ | ⟨v1, rest⟩
  · rfl
  rcases rest with _ | ⟨v2, rest⟩
  · rfl
  rcases rest with _ | ⟨v3, rest⟩ <;> rfl

private def RawAffineCoordinates.matrixEntry
    (data : RawAffineCoordinates) : ℕ → ℕ → ℤ
  | 0, 0 => data.m00
  | 0, 1 => data.m01
  | 0, 2 => data.m02
  | 0, 3 => data.m03
  | 1, 0 => data.m10
  | 1, 1 => data.m11
  | 1, 2 => data.m12
  | 1, 3 => data.m13
  | 2, 0 => data.m20
  | 2, 1 => data.m21
  | 2, 2 => data.m22
  | 2, 3 => data.m23
  | 3, 0 => data.m30
  | 3, 1 => data.m31
  | 3, 2 => data.m32
  | 3, 3 => data.m33
  | _, _ => 0

private def RawAffineCoordinates.vectorEntry
    (data : RawAffineCoordinates) : ℕ → ℤ
  | 0 => data.v0
  | 1 => data.v1
  | 2 => data.v2
  | 3 => data.v3
  | _ => 0

def certificateIndex (i : SymplecticIndex) : Fin 4 :=
  (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin (2 + 2)) i

def matrixOfData (data : List ℤ) :
    Matrix SymplecticIndex SymplecticIndex ℤ :=
  let coordinates := rawAffineCoordinatesOfList data
  fun i j =>
    coordinates.matrixEntry
      (certificateIndex i).val (certificateIndex j).val

def vectorOfData (data : List ℤ) : IntegralLattice :=
  let coordinates := rawAffineCoordinatesOfList data
  fun i => coordinates.vectorEntry (certificateIndex i).val

@[simp] theorem matrixOfData_apply
    (data : List ℤ) (i j : SymplecticIndex) :
    matrixOfData data i j =
      data.getD
        (4 * (certificateIndex i).val + (certificateIndex j).val) 0 := by
  unfold matrixOfData
  rw [rawAffineCoordinatesOfList_eq_getD]
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem vectorOfData_apply
    (data : List ℤ) (i : SymplecticIndex) :
    vectorOfData data i =
      data.getD (16 + (certificateIndex i).val) 0 := by
  unfold vectorOfData
  rw [rawAffineCoordinatesOfList_eq_getD]
  rcases i with i | i <;> fin_cases i <;> rfl

def isSymplecticData (data : List ℤ) : Bool :=
  let matrix := matrixOfData data
  decide
    (∀ i j : SymplecticIndex,
      (matrix * Matrix.J (Fin 2) ℤ * matrix.transpose) i j =
        Matrix.J (Fin 2) ℤ i j)

theorem matrixOfData_mem_symplectic
    {data : List ℤ} (h : isSymplecticData data = true) :
    matrixOfData data ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  have hs :
      ∀ i j : SymplecticIndex,
        (matrixOfData data * Matrix.J (Fin 2) ℤ *
            (matrixOfData data).transpose) i j =
          Matrix.J (Fin 2) ℤ i j :=
    of_decide_eq_true h
  rw [SymplecticGroup.mem_iff]
  ext i j
  exact hs i j

def gammaZeroOfData (data : List ℤ) :
    IntegralSymplecticCocycleInput.GammaZero :=
  if h : isSymplecticData data = true then
    { fst := vectorOfData data
      snd := ⟨matrixOfData data, matrixOfData_mem_symplectic h⟩ }
  else
    1

def generators :
    Finset IntegralSymplecticCocycleInput.GammaZero :=
  (generatorData.map gammaZeroOfData).toFinset

@[irreducible] noncomputable def basisElement (i : ℕ) :
    IntegralSymplecticCocycleInput.GammaZero :=
  gammaZeroOfData (basisData.getD i [])

@[irreducible] noncomputable def certificateBasis (i : Fin 425) :
    IntegralSymplecticCocycleInput.GammaZero :=
  basisElement i

@[irreducible] noncomputable def allElement (i : ℕ) :
    IntegralSymplecticCocycleInput.GammaZero :=
  gammaZeroOfData (allElementDataRow i).toList

@[irreducible] noncomputable def productIndex (i j : ℕ) : ℕ :=
  (productIndexDataRow i).getD j 0 |>.toNat

@[irreducible] noncomputable def tableIndex (i j : Fin 425) : Fin 73033 :=
  Fin.ofNat 73033 (productIndex i j)

@[irreducible] noncomputable def tableElement (k : Fin 73033) :
    IntegralSymplecticCocycleInput.GammaZero :=
  allElement k

def fullFactorCoefficient (row : List ℤ) (i : ℕ) : ℤ :=
  if i = 0 then -row.sum else row.getD (i - 1) 0

noncomputable def fullGramCoefficient (i j : ℕ) : ℤ :=
  (fullGramData.getD i []).getD j 0

def rawAffineProductMatchesArraySpec (xa ya za : Array ℤ) : Bool :=
  let matrixEntry (a : Array ℤ) (i j : ℕ) := a.getD (4 * i + j) 0
  let vectorEntry (a : Array ℤ) (i : ℕ) := a.getD (16 + i) 0
  (List.range 4).all fun i ↦
    decide
      (vectorEntry za i =
        vectorEntry xa i +
          ((List.range 4).map fun k ↦
            matrixEntry xa i k * vectorEntry ya k).sum) &&
    (List.range 4).all fun j ↦
      decide
        (matrixEntry za i j =
          ((List.range 4).map fun k ↦
            matrixEntry xa i k * matrixEntry ya k j).sum)

private def rawAffineCoordinatesGetD
    (a : Array ℤ) : RawAffineCoordinates where
  m00 := a.getD 0 0
  m01 := a.getD 1 0
  m02 := a.getD 2 0
  m03 := a.getD 3 0
  m10 := a.getD 4 0
  m11 := a.getD 5 0
  m12 := a.getD 6 0
  m13 := a.getD 7 0
  m20 := a.getD 8 0
  m21 := a.getD 9 0
  m22 := a.getD 10 0
  m23 := a.getD 11 0
  m30 := a.getD 12 0
  m31 := a.getD 13 0
  m32 := a.getD 14 0
  m33 := a.getD 15 0
  v0 := a.getD 16 0
  v1 := a.getD 17 0
  v2 := a.getD 18 0
  v3 := a.getD 19 0

private def rawAffineCoordinates (a : Array ℤ) : RawAffineCoordinates :=
  match a.toList with
  | m00 :: m01 :: m02 :: m03 ::
      m10 :: m11 :: m12 :: m13 ::
      m20 :: m21 :: m22 :: m23 ::
      m30 :: m31 :: m32 :: m33 ::
      v0 :: v1 :: v2 :: v3 :: _ =>
      { m00, m01, m02, m03
        m10, m11, m12, m13
        m20, m21, m22, m23
        m30, m31, m32, m33
        v0, v1, v2, v3 }
  | _ => rawAffineCoordinatesGetD a

private theorem rawAffineCoordinates_eq_getD (a : Array ℤ) :
    rawAffineCoordinates a = rawAffineCoordinatesGetD a := by
  rcases a with ⟨_ | ⟨m00, rest⟩⟩
  · rfl
  rcases rest with _ | ⟨m01, rest⟩
  · rfl
  rcases rest with _ | ⟨m02, rest⟩
  · rfl
  rcases rest with _ | ⟨m03, rest⟩
  · rfl
  rcases rest with _ | ⟨m10, rest⟩
  · rfl
  rcases rest with _ | ⟨m11, rest⟩
  · rfl
  rcases rest with _ | ⟨m12, rest⟩
  · rfl
  rcases rest with _ | ⟨m13, rest⟩
  · rfl
  rcases rest with _ | ⟨m20, rest⟩
  · rfl
  rcases rest with _ | ⟨m21, rest⟩
  · rfl
  rcases rest with _ | ⟨m22, rest⟩
  · rfl
  rcases rest with _ | ⟨m23, rest⟩
  · rfl
  rcases rest with _ | ⟨m30, rest⟩
  · rfl
  rcases rest with _ | ⟨m31, rest⟩
  · rfl
  rcases rest with _ | ⟨m32, rest⟩
  · rfl
  rcases rest with _ | ⟨m33, rest⟩
  · rfl
  rcases rest with _ | ⟨v0, rest⟩
  · rfl
  rcases rest with _ | ⟨v1, rest⟩
  · rfl
  rcases rest with _ | ⟨v2, rest⟩
  · rfl
  rcases rest with _ | ⟨v3, rest⟩ <;> rfl

def rawAffineProductMatchesArray (xa ya za : Array ℤ) : Bool :=
  let x := rawAffineCoordinates xa
  let y := rawAffineCoordinates ya
  let z := rawAffineCoordinates za
  let row0 :=
    decide
      (z.v0 =
        x.v0 +
          (x.m00 * y.v0 +
            (x.m01 * y.v1 +
              (x.m02 * y.v2 + (x.m03 * y.v3 + 0))))) &&
      (decide
        (z.m00 =
          x.m00 * y.m00 +
            (x.m01 * y.m10 +
              (x.m02 * y.m20 + (x.m03 * y.m30 + 0)))) &&
      (decide
        (z.m01 =
          x.m00 * y.m01 +
            (x.m01 * y.m11 +
              (x.m02 * y.m21 + (x.m03 * y.m31 + 0)))) &&
      (decide
        (z.m02 =
          x.m00 * y.m02 +
            (x.m01 * y.m12 +
              (x.m02 * y.m22 + (x.m03 * y.m32 + 0)))) &&
      (decide
        (z.m03 =
          x.m00 * y.m03 +
            (x.m01 * y.m13 +
              (x.m02 * y.m23 + (x.m03 * y.m33 + 0)))) &&
        true))))
  let row1 :=
    decide
      (z.v1 =
        x.v1 +
          (x.m10 * y.v0 +
            (x.m11 * y.v1 +
              (x.m12 * y.v2 + (x.m13 * y.v3 + 0))))) &&
      (decide
        (z.m10 =
          x.m10 * y.m00 +
            (x.m11 * y.m10 +
              (x.m12 * y.m20 + (x.m13 * y.m30 + 0)))) &&
      (decide
        (z.m11 =
          x.m10 * y.m01 +
            (x.m11 * y.m11 +
              (x.m12 * y.m21 + (x.m13 * y.m31 + 0)))) &&
      (decide
        (z.m12 =
          x.m10 * y.m02 +
            (x.m11 * y.m12 +
              (x.m12 * y.m22 + (x.m13 * y.m32 + 0)))) &&
      (decide
        (z.m13 =
          x.m10 * y.m03 +
            (x.m11 * y.m13 +
              (x.m12 * y.m23 + (x.m13 * y.m33 + 0)))) &&
        true))))
  let row2 :=
    decide
      (z.v2 =
        x.v2 +
          (x.m20 * y.v0 +
            (x.m21 * y.v1 +
              (x.m22 * y.v2 + (x.m23 * y.v3 + 0))))) &&
      (decide
        (z.m20 =
          x.m20 * y.m00 +
            (x.m21 * y.m10 +
              (x.m22 * y.m20 + (x.m23 * y.m30 + 0)))) &&
      (decide
        (z.m21 =
          x.m20 * y.m01 +
            (x.m21 * y.m11 +
              (x.m22 * y.m21 + (x.m23 * y.m31 + 0)))) &&
      (decide
        (z.m22 =
          x.m20 * y.m02 +
            (x.m21 * y.m12 +
              (x.m22 * y.m22 + (x.m23 * y.m32 + 0)))) &&
      (decide
        (z.m23 =
          x.m20 * y.m03 +
            (x.m21 * y.m13 +
              (x.m22 * y.m23 + (x.m23 * y.m33 + 0)))) &&
        true))))
  let row3 :=
    decide
      (z.v3 =
        x.v3 +
          (x.m30 * y.v0 +
            (x.m31 * y.v1 +
              (x.m32 * y.v2 + (x.m33 * y.v3 + 0))))) &&
      (decide
        (z.m30 =
          x.m30 * y.m00 +
            (x.m31 * y.m10 +
              (x.m32 * y.m20 + (x.m33 * y.m30 + 0)))) &&
      (decide
        (z.m31 =
          x.m30 * y.m01 +
            (x.m31 * y.m11 +
              (x.m32 * y.m21 + (x.m33 * y.m31 + 0)))) &&
      (decide
        (z.m32 =
          x.m30 * y.m02 +
            (x.m31 * y.m12 +
              (x.m32 * y.m22 + (x.m33 * y.m32 + 0)))) &&
      (decide
        (z.m33 =
          x.m30 * y.m03 +
            (x.m31 * y.m13 +
              (x.m32 * y.m23 + (x.m33 * y.m33 + 0)))) &&
        true))))
  row0 && (row1 && (row2 && (row3 && true)))

theorem rawAffineProductMatchesArray_eq_spec
    (x y z : Array ℤ) :
    rawAffineProductMatchesArray x y z =
      rawAffineProductMatchesArraySpec x y z := by
  unfold rawAffineProductMatchesArray
  rw [show rawAffineCoordinates x = rawAffineCoordinatesGetD x from
      rawAffineCoordinates_eq_getD x]
  rw [show rawAffineCoordinates y = rawAffineCoordinatesGetD y from
      rawAffineCoordinates_eq_getD y]
  rw [show rawAffineCoordinates z = rawAffineCoordinatesGetD z from
      rawAffineCoordinates_eq_getD z]
  rfl

def rawAffineProductMatches (x y z : List ℤ) : Bool :=
  rawAffineProductMatchesArray x.toArray y.toArray z.toArray

noncomputable def basisDataIsSymplectic : Bool :=
  basisData.all isSymplecticData

end AffineSymplecticCertificate

end ConnesRigidity
