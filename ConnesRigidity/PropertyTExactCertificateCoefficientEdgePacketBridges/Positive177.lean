


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive177
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_177 :
    coefficientPositivePacketTerms177 =
      (positiveEdgeTerms.drop 101952).take 576 := by
  unfold coefficientPositivePacketTerms177 coefficientPositivePacketRows177
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
