


import ConnesRigidity.PropertyTExactCertificateOrbitSymmetryComposition
import Mathlib.GroupTheory.GroupAction.Quotient










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

open Matrix

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0




theorem rawSignedMatrix_injective :
    Function.Injective
      (fun index : Fin 64 =>
        signedMatrixOfRow (symmetryData.getD index.val #[])) := by
  decide +kernel



theorem symmetryNormalizerRowChecks (index : Fin 64) :
    isSignedNormalizerRow (symmetryData.getD index.val #[]) = true := by
  apply orbitSymmetryNormalizerCheck_sound
    orbitSymmetryNormalizerCheck_valid index.val
  simp [(orbitSymmetryCompositionCheck_sound
    orbitSymmetryCompositionCheck_valid).1, symmetryCardinality]




theorem symmetryNormalizer_matrix_injective :
    Function.Injective
      (fun index : Fin 64 => (symmetryNormalizer index.val).matrix) := by
  intro left right heq
  apply rawSignedMatrix_injective
  change
    (signedNormalizerOfRow (symmetryData.getD left.val #[])).matrix =
      (signedNormalizerOfRow (symmetryData.getD right.val #[])).matrix at heq
  rw [signedNormalizerOfRow_matrix_of_check
    (symmetryNormalizerRowChecks left),
    signedNormalizerOfRow_matrix_of_check
      (symmetryNormalizerRowChecks right)] at heq
  exact heq




structure OrbitSymmetry where

  index : Fin 64
  deriving DecidableEq

namespace OrbitSymmetry



@[ext] theorem ext {left right : OrbitSymmetry}
    (heq : left.index = right.index) : left = right := by
  cases left
  cases right
  cases heq
  rfl



@[simps]
def equivFin : OrbitSymmetry ≃ Fin 64 where
  toFun symmetry := symmetry.index
  invFun index := ⟨index⟩
  left_inv symmetry := by cases symmetry; rfl
  right_inv _ := rfl

instance : Fintype OrbitSymmetry :=
  Fintype.ofEquiv (Fin 64) equivFin.symm

@[simp] theorem card : Fintype.card OrbitSymmetry = 64 := by
  simpa using Fintype.card_congr equivFin

instance : One OrbitSymmetry := ⟨⟨7⟩⟩



instance : Mul OrbitSymmetry where
  mul left right :=
    ⟨⟨symmetryMulIndex left.index.val right.index.val,
      symmetryMulIndex_lt left.index right.index⟩⟩


instance : Inv OrbitSymmetry where
  inv symmetry :=
    ⟨⟨inverseSymmetry symmetry.index.val,
      symmetryInverseIndex_lt symmetry.index⟩⟩

@[simp] theorem one_index : (1 : OrbitSymmetry).index = 7 := rfl

@[simp] theorem mul_index (left right : OrbitSymmetry) :
    (left * right).index.val =
      symmetryMulIndex left.index.val right.index.val := rfl

@[simp] theorem inv_index (symmetry : OrbitSymmetry) :
    symmetry⁻¹.index.val = inverseSymmetry symmetry.index.val := rfl



theorem matrix_mul (left right : OrbitSymmetry) :
    (symmetryNormalizer (left * right).index.val).matrix =
      (symmetryNormalizer left.index.val).matrix *
        (symmetryNormalizer right.index.val).matrix :=
  symmetryNormalizer_mul_matrix left.index right.index




theorem mul_assoc (left middle right : OrbitSymmetry) :
    (left * middle) * right = left * (middle * right) := by
  apply OrbitSymmetry.ext
  apply symmetryNormalizer_matrix_injective
  change
    (symmetryNormalizer ((left * middle) * right).index.val).matrix =
      (symmetryNormalizer (left * (middle * right)).index.val).matrix
  rw [matrix_mul, matrix_mul, matrix_mul, matrix_mul, Matrix.mul_assoc]



theorem one_mul (symmetry : OrbitSymmetry) : 1 * symmetry = symmetry := by
  apply OrbitSymmetry.ext
  apply symmetryNormalizer_matrix_injective
  change
    (symmetryNormalizer ((1 : OrbitSymmetry) * symmetry).index.val).matrix =
      (symmetryNormalizer symmetry.index.val).matrix
  have hidentity : (symmetryNormalizer 7).matrix =
      (1 : Matrix SymplecticIndex SymplecticIndex Int) := by
    simpa [symmetryIdentityIndex] using symmetryNormalizer_identity_matrix
  rw [matrix_mul, one_index]
  change
    (symmetryNormalizer 7).matrix *
      (symmetryNormalizer symmetry.index.val).matrix =
        (symmetryNormalizer symmetry.index.val).matrix
  rw [hidentity, Matrix.one_mul]


theorem inv_mul_cancel (symmetry : OrbitSymmetry) :
    symmetry⁻¹ * symmetry = 1 := by
  apply OrbitSymmetry.ext
  apply Fin.ext
  change symmetryMulIndex (inverseSymmetry symmetry.index.val)
    symmetry.index.val = 7
  simpa [symmetryIdentityIndex] using
    symmetryMulIndex_inverse_left symmetry.index


instance : Group OrbitSymmetry :=
  Group.ofLeftAxioms mul_assoc one_mul inv_mul_cancel



theorem automorphism_one : orbitSymmetry (1 : OrbitSymmetry).index = 1 := by
  have hidentity : (symmetryNormalizer 7).matrix =
      (1 : Matrix SymplecticIndex SymplecticIndex Int) := by
    simpa [symmetryIdentityIndex] using symmetryNormalizer_identity_matrix
  apply MulEquiv.ext
  intro element
  apply CocycleExtension.ext
  · change (symmetryNormalizer 7).matrix.mulVec element.fst = element.fst
    rw [hidentity, Matrix.one_mulVec]
  · apply Subtype.ext
    change
      (symmetryNormalizer 7).matrix *
          (element.snd : Matrix SymplecticIndex SymplecticIndex Int) *
            (symmetryNormalizer 7).matrix.transpose =
        (element.snd : Matrix SymplecticIndex SymplecticIndex Int)
    rw [hidentity]
    simp



theorem automorphism_mul (left right : OrbitSymmetry) :
    orbitSymmetry (left * right).index =
      (orbitSymmetry right.index).trans (orbitSymmetry left.index) := by
  change
    (symmetryNormalizer (left * right).index.val).gammaZeroEquiv =
      (symmetryNormalizer right.index.val).gammaZeroEquiv.trans
        (symmetryNormalizer left.index.val).gammaZeroEquiv
  exact (SignedNormalizer.gammaZeroEquiv_trans_of_matrix_mul
    (symmetryNormalizer left.index.val)
    (symmetryNormalizer right.index.val)
    (symmetryNormalizer (left * right).index.val)
    (matrix_mul left right)).symm



def automorphismHom : OrbitSymmetry →* MulAut constructedGammaZeroGroup where
  toFun symmetry := orbitSymmetry symmetry.index
  map_one' := automorphism_one
  map_mul' left right := automorphism_mul left right

@[simp] theorem automorphismHom_apply
    (symmetry : OrbitSymmetry) :
    automorphismHom symmetry = orbitSymmetry symmetry.index := rfl



instance : MulAction OrbitSymmetry constructedGammaZeroGroup where
  smul symmetry element := orbitSymmetry symmetry.index element
  one_smul element := by
    change (automorphismHom 1) element = element
    rw [map_one]
    rfl
  mul_smul left right element := by
    change (automorphismHom (left * right)) element =
      (automorphismHom left) ((automorphismHom right) element)
    rw [map_mul]
    rfl

@[simp] theorem smul_def (symmetry : OrbitSymmetry)
    (element : constructedGammaZeroGroup) :
    symmetry • element = orbitSymmetry symmetry.index element := rfl

end OrbitSymmetry



theorem orbitSymmetry_mul (left right : OrbitSymmetry) :
    orbitSymmetry (left * right).index =
      (orbitSymmetry right.index).trans (orbitSymmetry left.index) :=
  OrbitSymmetry.automorphism_mul left right


@[simp] theorem card_orbitSymmetry : Fintype.card OrbitSymmetry = 64 :=
  OrbitSymmetry.card

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
