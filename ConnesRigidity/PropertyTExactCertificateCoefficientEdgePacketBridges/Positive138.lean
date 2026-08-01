


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive138
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_138 :
    coefficientPositivePacketTerms138 =
      (positiveEdgeTerms.drop 79488).take 576 := by
  unfold coefficientPositivePacketTerms138 coefficientPositivePacketRows138
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
