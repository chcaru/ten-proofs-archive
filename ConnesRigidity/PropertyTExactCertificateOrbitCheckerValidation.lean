


import ConnesRigidity.PropertyTExactCertificateOrbitCheckers










namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


theorem coefficientEquationData_size : coefficientEquationData.size = 537 := by
  decide +kernel


theorem coefficientTermData_size : coefficientTermData.size = 1798 := by
  decide +kernel


theorem orbitCoefficientRowCheck_000 : orbitCoefficientRowCheck 0 = true := by
  decide +kernel







def orbitConsumeCoefficientTerms (key : Int) :
    Nat → List (Array Int) → Int → Option (Int × List (Array Int))
  | 0, rows, total => some (total, rows)
  | _ + 1, [], _ => none
  | remaining + 1, row :: tail, total =>
      if row.size = coefficientTermRowWidth ∧ orbitEntry row 0 = key then
        orbitConsumeCoefficientTerms key remaining tail
          (total + orbitCoefficientTermValue row)
      else
        none









def orbitCoefficientStreamingCheck :
    List (Array Int) → List (Array Int) → Nat → Bool
  | [], terms, _ => terms.isEmpty
  | row :: equations, terms, position =>
      let key := orbitEntry row 0
      let start := orbitEntry row 1
      let count := orbitEntry row 2
      if row.size = coefficientEquationRowWidth ∧
          start = (position : Int) ∧ 0 ≤ count then
        match orbitConsumeCoefficientTerms key count.toNat terms 0 with
        | none => false
        | some (total, remaining) =>
            decide (total = orbitEntry row 3) &&
              orbitCoefficientStreamingCheck equations remaining
                (position + count.toNat)
      else
        false


theorem orbitCoefficientStreamingCheck_valid :
    orbitCoefficientStreamingCheck coefficientEquationData.toList
      coefficientTermData.toList 0 = true := by
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
