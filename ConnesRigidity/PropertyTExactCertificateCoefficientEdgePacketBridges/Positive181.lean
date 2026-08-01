
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive181
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_181 :
    coefficientPositivePacketTerms181 =
      (positiveEdgeTerms.drop 104256).take 576 := by
  unfold coefficientPositivePacketTerms181 coefficientPositivePacketRows181
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
