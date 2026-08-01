


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive218
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_218 :
    coefficientPositivePacketTerms218 =
      (positiveEdgeTerms.drop 125568).take 576 := by
  unfold coefficientPositivePacketTerms218 coefficientPositivePacketRows218
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
