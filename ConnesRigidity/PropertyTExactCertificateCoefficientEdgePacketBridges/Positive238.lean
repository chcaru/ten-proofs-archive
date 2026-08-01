


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive238
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_238 :
    coefficientPositivePacketTerms238 =
      (positiveEdgeTerms.drop 137088).take 576 := by
  unfold coefficientPositivePacketTerms238 coefficientPositivePacketRows238
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
