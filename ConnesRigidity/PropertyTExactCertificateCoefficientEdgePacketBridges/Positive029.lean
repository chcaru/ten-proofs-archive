


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive029
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_029 :
    coefficientPositivePacketTerms029 =
      (positiveEdgeTerms.drop 16704).take 576 := by
  unfold coefficientPositivePacketTerms029 coefficientPositivePacketRows029
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
