
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive128
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_128 :
    coefficientPositivePacketTerms128 =
      (positiveEdgeTerms.drop 73728).take 576 := by
  unfold coefficientPositivePacketTerms128 coefficientPositivePacketRows128
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
