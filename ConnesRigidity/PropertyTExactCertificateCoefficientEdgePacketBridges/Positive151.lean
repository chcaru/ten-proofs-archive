
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive151
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_151 :
    coefficientPositivePacketTerms151 =
      (positiveEdgeTerms.drop 86976).take 576 := by
  unfold coefficientPositivePacketTerms151 coefficientPositivePacketRows151
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
