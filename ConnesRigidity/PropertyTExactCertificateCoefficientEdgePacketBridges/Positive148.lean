
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive148
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_148 :
    coefficientPositivePacketTerms148 =
      (positiveEdgeTerms.drop 85248).take 576 := by
  unfold coefficientPositivePacketTerms148 coefficientPositivePacketRows148
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
