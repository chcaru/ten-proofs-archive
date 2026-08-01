
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive058
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_058 :
    coefficientPositivePacketTerms058 =
      (positiveEdgeTerms.drop 33408).take 576 := by
  unfold coefficientPositivePacketTerms058 coefficientPositivePacketRows058
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
