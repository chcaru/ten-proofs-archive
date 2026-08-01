
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive192
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_192 :
    coefficientPositivePacketTerms192 =
      (positiveEdgeTerms.drop 110592).take 576 := by
  unfold coefficientPositivePacketTerms192 coefficientPositivePacketRows192
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
