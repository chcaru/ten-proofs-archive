


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive209
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_209 :
    coefficientPositivePacketTerms209 =
      (positiveEdgeTerms.drop 120384).take 576 := by
  unfold coefficientPositivePacketTerms209 coefficientPositivePacketRows209
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
