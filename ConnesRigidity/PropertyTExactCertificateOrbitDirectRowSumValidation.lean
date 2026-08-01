


import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row00
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row01
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row02
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row03
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row04
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row05
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row06
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row07
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row08
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row09
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row10
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row11
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row12
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row13
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row14
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row15
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row16
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row17
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row18
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row19
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row20
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row21
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row22
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row23
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row24
import ConnesRigidity.PropertyTExactCertificateOrbitDirectRowSumValidations.Row25
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases



namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000

def orbitNormalizedRowGramSum (row : Nat) : Int :=
  (pairOrbitIndexData.getD row #[]).toList.foldl
    (fun total orbit => total + gramOrbitCoefficient orbit.toNat) 0




theorem orbitNormalizedRowGramSum_zero (row : Fin 26) :
    orbitNormalizedRowGramSum row.val = 0 := by
  unfold orbitNormalizedRowGramSum
  fin_cases row <;>
    first
    | exact orbitNormalizedRowGramSum_00
    | exact orbitNormalizedRowGramSum_01
    | exact orbitNormalizedRowGramSum_02
    | exact orbitNormalizedRowGramSum_03
    | exact orbitNormalizedRowGramSum_04
    | exact orbitNormalizedRowGramSum_05
    | exact orbitNormalizedRowGramSum_06
    | exact orbitNormalizedRowGramSum_07
    | exact orbitNormalizedRowGramSum_08
    | exact orbitNormalizedRowGramSum_09
    | exact orbitNormalizedRowGramSum_10
    | exact orbitNormalizedRowGramSum_11
    | exact orbitNormalizedRowGramSum_12
    | exact orbitNormalizedRowGramSum_13
    | exact orbitNormalizedRowGramSum_14
    | exact orbitNormalizedRowGramSum_15
    | exact orbitNormalizedRowGramSum_16
    | exact orbitNormalizedRowGramSum_17
    | exact orbitNormalizedRowGramSum_18
    | exact orbitNormalizedRowGramSum_19
    | exact orbitNormalizedRowGramSum_20
    | exact orbitNormalizedRowGramSum_21
    | exact orbitNormalizedRowGramSum_22
    | exact orbitNormalizedRowGramSum_23
    | exact orbitNormalizedRowGramSum_24
    | exact orbitNormalizedRowGramSum_25

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
