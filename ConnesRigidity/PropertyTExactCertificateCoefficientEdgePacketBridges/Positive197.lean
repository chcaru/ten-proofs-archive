
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive197
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_197 :
    coefficientPositivePacketTerms197 =
      (positiveEdgeTerms.drop 113472).take 576 := by
  unfold coefficientPositivePacketTerms197 coefficientPositivePacketRows197
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
