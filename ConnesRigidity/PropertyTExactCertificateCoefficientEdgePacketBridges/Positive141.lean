
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive141
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_141 :
    coefficientPositivePacketTerms141 =
      (positiveEdgeTerms.drop 81216).take 576 := by
  unfold coefficientPositivePacketTerms141 coefficientPositivePacketRows141
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
