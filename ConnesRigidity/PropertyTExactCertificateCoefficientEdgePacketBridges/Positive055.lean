


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive055
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_055 :
    coefficientPositivePacketTerms055 =
      (positiveEdgeTerms.drop 31680).take 576 := by
  unfold coefficientPositivePacketTerms055 coefficientPositivePacketRows055
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
