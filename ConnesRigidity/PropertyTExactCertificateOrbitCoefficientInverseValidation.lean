
import ConnesRigidity.PropertyTExactCertificateOrbitStabilizerValidation

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def orbitCoefficientInverseRowsCheck :
    List (Array Int) → List (Array Int) → Bool
  | row :: rows, inverse :: inverses =>
      isSymplecticRow row &&
        rawProductCheck row inverse orbitIdentityRow &&
        orbitCoefficientInverseRowsCheck rows inverses
  | [], [] => true
  | _, _ => false

theorem orbitCoefficientInverseRowsCheck_valid :
    orbitCoefficientInverseRowsCheck
      coefficientRepresentativeData.toList
      coefficientInverseRepresentativeData.toList = true := by
  unfold orbitCoefficientInverseRowsCheck isSymplecticRow rawProductCheck
    coefficientRepresentativeData coefficientInverseRepresentativeData
    orbitIdentityRow
  decide +kernel

end

end ConnesRigidity.AffineSymplecticOrbitCertificate
