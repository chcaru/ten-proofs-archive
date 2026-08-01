
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedComparator
import ConnesRigidity.PropertyTExactCertificateOrbitCanonicalPackedData

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

def coefficientCanonicalPackedImagesCheck
    (canonical representative inverse : Nat)
    (actions : List (List Int)) : Bool :=
  actions.all fun action =>
    match action with
    | [_index, packed] =>
        canonicalPackedCoordinateLE canonical packed.toNat
          representative 20 &&
        canonicalPackedCoordinateLE canonical packed.toNat
          inverse 20
    | _ => false

def coefficientCanonicalPackedWitnessRowCheck (row : List Int) : Bool :=
  match row with
  | [_orbit, canonical, representative, inverse] =>
      coefficientCanonicalPackedImagesCheck canonical.toNat
        representative.toNat inverse.toNat canonicalPackedActionData
  | _ => false

def coefficientCanonicalPackedWitnessRowsCheck
    (actions : List (List Int)) : List (List Int) → Bool
  | [] => true
  | [_orbit, canonical, representative, inverse] :: remaining =>
      coefficientCanonicalPackedImagesCheck canonical.toNat
        representative.toNat inverse.toNat actions &&
        coefficientCanonicalPackedWitnessRowsCheck actions remaining
  | _ :: _ => false

theorem coefficientCanonicalPackedWitnessRowsCheck_get
    (actions rows : List (List Int))
    (index : Nat) (hindex : index < rows.length)
    (hcheck : coefficientCanonicalPackedWitnessRowsCheck actions rows = true) :
    match rows[index] with
    | [_orbit, canonical, representative, inverse] =>
        coefficientCanonicalPackedImagesCheck canonical.toNat
          representative.toNat inverse.toNat actions = true
    | _ => False := by
  induction rows generalizing index with
  | nil => simp at hindex
  | cons row rows ih =>
    cases row with
    | nil => simp [coefficientCanonicalPackedWitnessRowsCheck] at hcheck
    | cons orbit rest =>
      cases rest with
      | nil => simp [coefficientCanonicalPackedWitnessRowsCheck] at hcheck
      | cons canonical rest =>
        cases rest with
        | nil => simp [coefficientCanonicalPackedWitnessRowsCheck] at hcheck
        | cons representative rest =>
          cases rest with
          | nil => simp [coefficientCanonicalPackedWitnessRowsCheck] at hcheck
          | cons inverse rest =>
            cases rest with
            | cons _ _ =>
                simp [coefficientCanonicalPackedWitnessRowsCheck] at hcheck
            | nil =>
                simp only [coefficientCanonicalPackedWitnessRowsCheck,
                  Bool.and_eq_true] at hcheck
                cases index with
                | zero => exact hcheck.1
                | succ index =>
                    exact ih index (by simpa using hindex) hcheck.2

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
