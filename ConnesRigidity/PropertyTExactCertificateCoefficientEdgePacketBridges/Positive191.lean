
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive191
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_191 :
    coefficientPositivePacketTerms191 =
      (positiveEdgeTerms.drop 110016).take 576 := by
  unfold coefficientPositivePacketTerms191 coefficientPositivePacketRows191
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
