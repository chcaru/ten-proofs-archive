
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive086
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_086 :
    coefficientPositivePacketTerms086 =
      (positiveEdgeTerms.drop 49536).take 576 := by
  unfold coefficientPositivePacketTerms086 coefficientPositivePacketRows086
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
