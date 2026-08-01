
import ConnesRigidity.PropertyTExactCertificateOrbitCheckers
import Mathlib.Tactic.IntervalCases
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row000
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row001
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row002
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row003
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row004
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row005
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row006
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row007
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row008
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row009
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row010
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row011
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row012
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row013
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row014
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row015
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row016
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row017
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row018
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row019
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row020
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row021
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row022
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row023
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row024
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row025
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row026
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row027
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row028
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row029
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row030
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row031
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row032
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row033
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row034
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row035
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row036
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row037
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row038
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row039
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row040
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row041
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row042
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row043
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row044
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row045
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row046
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row047
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row048
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row049
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row050
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row051
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row052
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row053
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row054
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row055
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row056
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row057
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row058
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row059
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row060
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row061
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row062
import ConnesRigidity.PropertyTExactCertificateOrbitTransportRows.Row063

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem orbitPairCoverageCheck_valid : orbitPairCoverageCheck = true := by
  decide +kernel

theorem orbitBasisPermutationCheck_valid :
    orbitBasisPermutationCheck = true := by
  decide +kernel

theorem orbitBasisTransportCheck_valid : orbitBasisTransportCheck = true := by
  decide +kernel

theorem orbitSymmetryInverseCheck_valid : orbitSymmetryInverseCheck = true := by
  unfold orbitSymmetryInverseCheck
  simp only [Bool.and_eq_true]
  constructor
  · decide +kernel
  · rw [List.all_eq_true]
    intro index hindex
    have hsize : symmetryInverseData.size = 64 := by
      decide +kernel
    have hindex' : index < 64 := by
      simpa [hsize] using List.mem_range.mp hindex
    interval_cases index
    · exact orbitSymmetryInverseRowCheck_000_valid
    · exact orbitSymmetryInverseRowCheck_001_valid
    · exact orbitSymmetryInverseRowCheck_002_valid
    · exact orbitSymmetryInverseRowCheck_003_valid
    · exact orbitSymmetryInverseRowCheck_004_valid
    · exact orbitSymmetryInverseRowCheck_005_valid
    · exact orbitSymmetryInverseRowCheck_006_valid
    · exact orbitSymmetryInverseRowCheck_007_valid
    · exact orbitSymmetryInverseRowCheck_008_valid
    · exact orbitSymmetryInverseRowCheck_009_valid
    · exact orbitSymmetryInverseRowCheck_010_valid
    · exact orbitSymmetryInverseRowCheck_011_valid
    · exact orbitSymmetryInverseRowCheck_012_valid
    · exact orbitSymmetryInverseRowCheck_013_valid
    · exact orbitSymmetryInverseRowCheck_014_valid
    · exact orbitSymmetryInverseRowCheck_015_valid
    · exact orbitSymmetryInverseRowCheck_016_valid
    · exact orbitSymmetryInverseRowCheck_017_valid
    · exact orbitSymmetryInverseRowCheck_018_valid
    · exact orbitSymmetryInverseRowCheck_019_valid
    · exact orbitSymmetryInverseRowCheck_020_valid
    · exact orbitSymmetryInverseRowCheck_021_valid
    · exact orbitSymmetryInverseRowCheck_022_valid
    · exact orbitSymmetryInverseRowCheck_023_valid
    · exact orbitSymmetryInverseRowCheck_024_valid
    · exact orbitSymmetryInverseRowCheck_025_valid
    · exact orbitSymmetryInverseRowCheck_026_valid
    · exact orbitSymmetryInverseRowCheck_027_valid
    · exact orbitSymmetryInverseRowCheck_028_valid
    · exact orbitSymmetryInverseRowCheck_029_valid
    · exact orbitSymmetryInverseRowCheck_030_valid
    · exact orbitSymmetryInverseRowCheck_031_valid
    · exact orbitSymmetryInverseRowCheck_032_valid
    · exact orbitSymmetryInverseRowCheck_033_valid
    · exact orbitSymmetryInverseRowCheck_034_valid
    · exact orbitSymmetryInverseRowCheck_035_valid
    · exact orbitSymmetryInverseRowCheck_036_valid
    · exact orbitSymmetryInverseRowCheck_037_valid
    · exact orbitSymmetryInverseRowCheck_038_valid
    · exact orbitSymmetryInverseRowCheck_039_valid
    · exact orbitSymmetryInverseRowCheck_040_valid
    · exact orbitSymmetryInverseRowCheck_041_valid
    · exact orbitSymmetryInverseRowCheck_042_valid
    · exact orbitSymmetryInverseRowCheck_043_valid
    · exact orbitSymmetryInverseRowCheck_044_valid
    · exact orbitSymmetryInverseRowCheck_045_valid
    · exact orbitSymmetryInverseRowCheck_046_valid
    · exact orbitSymmetryInverseRowCheck_047_valid
    · exact orbitSymmetryInverseRowCheck_048_valid
    · exact orbitSymmetryInverseRowCheck_049_valid
    · exact orbitSymmetryInverseRowCheck_050_valid
    · exact orbitSymmetryInverseRowCheck_051_valid
    · exact orbitSymmetryInverseRowCheck_052_valid
    · exact orbitSymmetryInverseRowCheck_053_valid
    · exact orbitSymmetryInverseRowCheck_054_valid
    · exact orbitSymmetryInverseRowCheck_055_valid
    · exact orbitSymmetryInverseRowCheck_056_valid
    · exact orbitSymmetryInverseRowCheck_057_valid
    · exact orbitSymmetryInverseRowCheck_058_valid
    · exact orbitSymmetryInverseRowCheck_059_valid
    · exact orbitSymmetryInverseRowCheck_060_valid
    · exact orbitSymmetryInverseRowCheck_061_valid
    · exact orbitSymmetryInverseRowCheck_062_valid
    · exact orbitSymmetryInverseRowCheck_063_valid

end ConnesRigidity.AffineSymplecticOrbitCertificate
