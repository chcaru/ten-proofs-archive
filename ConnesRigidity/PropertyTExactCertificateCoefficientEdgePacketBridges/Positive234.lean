
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive234
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_234 :
    coefficientPositivePacketTerms234 =
      (positiveEdgeTerms.drop 134784).take 576 := by
  unfold coefficientPositivePacketTerms234 coefficientPositivePacketRows234
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
