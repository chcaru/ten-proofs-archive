
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive084
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_084 :
    coefficientPositivePacketTerms084 =
      (positiveEdgeTerms.drop 48384).take 576 := by
  unfold coefficientPositivePacketTerms084 coefficientPositivePacketRows084
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
