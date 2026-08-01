


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive216
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_216 :
    coefficientPositivePacketTerms216 =
      (positiveEdgeTerms.drop 124416).take 576 := by
  unfold coefficientPositivePacketTerms216 coefficientPositivePacketRows216
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
