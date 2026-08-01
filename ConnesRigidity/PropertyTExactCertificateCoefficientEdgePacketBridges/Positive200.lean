
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive200
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_200 :
    coefficientPositivePacketTerms200 =
      (positiveEdgeTerms.drop 115200).take 576 := by
  unfold coefficientPositivePacketTerms200 coefficientPositivePacketRows200
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
