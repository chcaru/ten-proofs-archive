
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive143
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_143 :
    coefficientPositivePacketTerms143 =
      (positiveEdgeTerms.drop 82368).take 576 := by
  unfold coefficientPositivePacketTerms143 coefficientPositivePacketRows143
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
