


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive247
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_247 :
    coefficientPositivePacketTerms247 =
      (positiveEdgeTerms.drop 142272).take 576 := by
  unfold coefficientPositivePacketTerms247 coefficientPositivePacketRows247
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
