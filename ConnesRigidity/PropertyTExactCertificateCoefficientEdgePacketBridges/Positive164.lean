
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive164
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_164 :
    coefficientPositivePacketTerms164 =
      (positiveEdgeTerms.drop 94464).take 576 := by
  unfold coefficientPositivePacketTerms164 coefficientPositivePacketRows164
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
