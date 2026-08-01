
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive008
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_008 :
    coefficientPositivePacketTerms008 =
      (positiveEdgeTerms.drop 4608).take 576 := by
  unfold coefficientPositivePacketTerms008 coefficientPositivePacketRows008
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
