


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive102
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_102 :
    coefficientPositivePacketTerms102 =
      (positiveEdgeTerms.drop 58752).take 576 := by
  unfold coefficientPositivePacketTerms102 coefficientPositivePacketRows102
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
