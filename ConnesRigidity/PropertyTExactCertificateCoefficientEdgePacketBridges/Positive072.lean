
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive072
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_072 :
    coefficientPositivePacketTerms072 =
      (positiveEdgeTerms.drop 41472).take 576 := by
  unfold coefficientPositivePacketTerms072 coefficientPositivePacketRows072
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
