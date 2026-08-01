
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive223
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_223 :
    coefficientPositivePacketTerms223 =
      (positiveEdgeTerms.drop 128448).take 576 := by
  unfold coefficientPositivePacketTerms223 coefficientPositivePacketRows223
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
