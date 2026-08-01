
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive154
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_154 :
    coefficientPositivePacketTerms154 =
      (positiveEdgeTerms.drop 88704).take 576 := by
  unfold coefficientPositivePacketTerms154 coefficientPositivePacketRows154
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
