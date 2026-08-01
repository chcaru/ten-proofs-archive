
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive230
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_230 :
    coefficientPositivePacketTerms230 =
      (positiveEdgeTerms.drop 132480).take 576 := by
  unfold coefficientPositivePacketTerms230 coefficientPositivePacketRows230
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
