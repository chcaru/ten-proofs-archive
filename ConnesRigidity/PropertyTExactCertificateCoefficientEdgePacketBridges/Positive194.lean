
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive194
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_194 :
    coefficientPositivePacketTerms194 =
      (positiveEdgeTerms.drop 111744).take 576 := by
  unfold coefficientPositivePacketTerms194 coefficientPositivePacketRows194
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
