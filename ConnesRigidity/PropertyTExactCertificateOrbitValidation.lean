


import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block00
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block01
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block02
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block03
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block04
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block05
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block06
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block07
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block08
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block09
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block10
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block11
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block12
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block13
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block14
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block15
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block16
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block17
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block18
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block19
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block20
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block21
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block22
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block23
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block24
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block25
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block26
import ConnesRigidity.PropertyTExactCertificateOrbitBlockValidations.Block27


namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000



theorem orbitBlockChecks (block : Fin 28) :
    blockFactorIdentityBlockCheck block.val = true ∧
      blockResidualSymmetryBlockCheck block.val = true ∧
      blockResidualDominanceBlockCheck block.val = true := by
  fin_cases block <;>
    first
    | exact ⟨orbitBlockFactorIdentityBlockCheck_00,
        orbitBlockResidualSymmetryBlockCheck_00,
        orbitBlockResidualDominanceBlockCheck_00⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_01,
        orbitBlockResidualSymmetryBlockCheck_01,
        orbitBlockResidualDominanceBlockCheck_01⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_02,
        orbitBlockResidualSymmetryBlockCheck_02,
        orbitBlockResidualDominanceBlockCheck_02⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_03,
        orbitBlockResidualSymmetryBlockCheck_03,
        orbitBlockResidualDominanceBlockCheck_03⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_04,
        orbitBlockResidualSymmetryBlockCheck_04,
        orbitBlockResidualDominanceBlockCheck_04⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_05,
        orbitBlockResidualSymmetryBlockCheck_05,
        orbitBlockResidualDominanceBlockCheck_05⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_06,
        orbitBlockResidualSymmetryBlockCheck_06,
        orbitBlockResidualDominanceBlockCheck_06⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_07,
        orbitBlockResidualSymmetryBlockCheck_07,
        orbitBlockResidualDominanceBlockCheck_07⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_08,
        orbitBlockResidualSymmetryBlockCheck_08,
        orbitBlockResidualDominanceBlockCheck_08⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_09,
        orbitBlockResidualSymmetryBlockCheck_09,
        orbitBlockResidualDominanceBlockCheck_09⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_10,
        orbitBlockResidualSymmetryBlockCheck_10,
        orbitBlockResidualDominanceBlockCheck_10⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_11,
        orbitBlockResidualSymmetryBlockCheck_11,
        orbitBlockResidualDominanceBlockCheck_11⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_12,
        orbitBlockResidualSymmetryBlockCheck_12,
        orbitBlockResidualDominanceBlockCheck_12⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_13,
        orbitBlockResidualSymmetryBlockCheck_13,
        orbitBlockResidualDominanceBlockCheck_13⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_14,
        orbitBlockResidualSymmetryBlockCheck_14,
        orbitBlockResidualDominanceBlockCheck_14⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_15,
        orbitBlockResidualSymmetryBlockCheck_15,
        orbitBlockResidualDominanceBlockCheck_15⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_16,
        orbitBlockResidualSymmetryBlockCheck_16,
        orbitBlockResidualDominanceBlockCheck_16⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_17,
        orbitBlockResidualSymmetryBlockCheck_17,
        orbitBlockResidualDominanceBlockCheck_17⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_18,
        orbitBlockResidualSymmetryBlockCheck_18,
        orbitBlockResidualDominanceBlockCheck_18⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_19,
        orbitBlockResidualSymmetryBlockCheck_19,
        orbitBlockResidualDominanceBlockCheck_19⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_20,
        orbitBlockResidualSymmetryBlockCheck_20,
        orbitBlockResidualDominanceBlockCheck_20⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_21,
        orbitBlockResidualSymmetryBlockCheck_21,
        orbitBlockResidualDominanceBlockCheck_21⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_22,
        orbitBlockResidualSymmetryBlockCheck_22,
        orbitBlockResidualDominanceBlockCheck_22⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_23,
        orbitBlockResidualSymmetryBlockCheck_23,
        orbitBlockResidualDominanceBlockCheck_23⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_24,
        orbitBlockResidualSymmetryBlockCheck_24,
        orbitBlockResidualDominanceBlockCheck_24⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_25,
        orbitBlockResidualSymmetryBlockCheck_25,
        orbitBlockResidualDominanceBlockCheck_25⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_26,
        orbitBlockResidualSymmetryBlockCheck_26,
        orbitBlockResidualDominanceBlockCheck_26⟩
    | exact ⟨orbitBlockFactorIdentityBlockCheck_27,
        orbitBlockResidualSymmetryBlockCheck_27,
        orbitBlockResidualDominanceBlockCheck_27⟩



theorem orbitBlockFactorIdentityChecks
    (block : Fin 28)
    (row column : Fin (blockDimension block.val)) :
    blockFactorIdentityEntryCheck block.val row.val column.val = true :=
  blockFactorIdentityBlockCheck_sound block.val
    (orbitBlockChecks block).1 row column


theorem orbitBlockResidualSymmetryChecks
    (block : Fin 28)
    (row column : Fin (blockDimension block.val)) :
    blockResidualSymmetricEntryCheck block.val row.val column.val = true :=
  blockResidualSymmetryBlockCheck_sound block.val
    (orbitBlockChecks block).2.1 row column


theorem orbitBlockResidualDominanceChecks
    (block : Fin 28)
    (row : Fin (blockDimension block.val)) :
    blockResidualDominanceRowCheck block.val row.val = true :=
  blockResidualDominanceBlockCheck_sound block.val
    (orbitBlockChecks block).2.2 row

end ConnesRigidity.AffineSymplecticOrbitCertificate
