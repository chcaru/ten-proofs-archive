
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive235
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_235 :
    coefficientPositivePacketTerms235 =
      (positiveEdgeTerms.drop 135360).take 576 := by
  unfold coefficientPositivePacketTerms235 coefficientPositivePacketRows235
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
