


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive125
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_125 :
    coefficientPositivePacketTerms125 =
      (positiveEdgeTerms.drop 72000).take 576 := by
  unfold coefficientPositivePacketTerms125 coefficientPositivePacketRows125
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
