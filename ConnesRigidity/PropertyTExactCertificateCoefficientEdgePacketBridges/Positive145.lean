
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive145
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_145 :
    coefficientPositivePacketTerms145 =
      (positiveEdgeTerms.drop 83520).take 576 := by
  unfold coefficientPositivePacketTerms145 coefficientPositivePacketRows145
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
