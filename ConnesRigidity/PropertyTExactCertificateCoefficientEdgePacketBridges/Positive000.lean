


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive000
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_000 :
    coefficientPositivePacketTerms000 =
      (positiveEdgeTerms.drop 0).take 576 := by
  unfold coefficientPositivePacketTerms000 coefficientPositivePacketRows000
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
