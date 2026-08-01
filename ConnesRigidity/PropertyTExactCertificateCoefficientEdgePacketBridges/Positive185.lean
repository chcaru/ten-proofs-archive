
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive185
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_185 :
    coefficientPositivePacketTerms185 =
      (positiveEdgeTerms.drop 106560).take 576 := by
  unfold coefficientPositivePacketTerms185 coefficientPositivePacketRows185
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
