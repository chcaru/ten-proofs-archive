
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive075
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_075 :
    coefficientPositivePacketTerms075 =
      (positiveEdgeTerms.drop 43200).take 576 := by
  unfold coefficientPositivePacketTerms075 coefficientPositivePacketRows075
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
