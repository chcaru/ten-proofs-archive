
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row00
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row01
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row02
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row03
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row04
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row05
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row06
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row07
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row08
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row09
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row10
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row11
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row12
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row13
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row14
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row15
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row16
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row17
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row18
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row19
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row20
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row21
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row22
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row23
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row24
import ConnesRigidity.PropertyTExactCertificateOrbitRowSumValidations.Row25
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000

theorem rowSumEquationData_size : rowSumEquationData.size = 26 := by
  decide +kernel

theorem basisOrbitRepresentativeData_size :
    basisOrbitRepresentativeData.size = 26 := by
  decide +kernel

theorem orbitRowSumRowChecks (row : Fin 26) :
    orbitRowSumRowCheck row.val = true := by
  fin_cases row <;>
    first
    | exact orbitRowSumRowCheck_00
    | exact orbitRowSumRowCheck_01
    | exact orbitRowSumRowCheck_02
    | exact orbitRowSumRowCheck_03
    | exact orbitRowSumRowCheck_04
    | exact orbitRowSumRowCheck_05
    | exact orbitRowSumRowCheck_06
    | exact orbitRowSumRowCheck_07
    | exact orbitRowSumRowCheck_08
    | exact orbitRowSumRowCheck_09
    | exact orbitRowSumRowCheck_10
    | exact orbitRowSumRowCheck_11
    | exact orbitRowSumRowCheck_12
    | exact orbitRowSumRowCheck_13
    | exact orbitRowSumRowCheck_14
    | exact orbitRowSumRowCheck_15
    | exact orbitRowSumRowCheck_16
    | exact orbitRowSumRowCheck_17
    | exact orbitRowSumRowCheck_18
    | exact orbitRowSumRowCheck_19
    | exact orbitRowSumRowCheck_20
    | exact orbitRowSumRowCheck_21
    | exact orbitRowSumRowCheck_22
    | exact orbitRowSumRowCheck_23
    | exact orbitRowSumRowCheck_24
    | exact orbitRowSumRowCheck_25

theorem orbitRowSumCheck_valid : orbitRowSumCheck = true := by
  unfold orbitRowSumCheck
  rw [rowSumEquationData_size, basisOrbitRepresentativeData_size]
  have hrows : (List.range 26).all orbitRowSumRowCheck = true := by
    apply List.all_eq_true.mpr
    intro row hrow
    exact orbitRowSumRowChecks ⟨row, List.mem_range.mp hrow⟩
  simpa using hrows

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
