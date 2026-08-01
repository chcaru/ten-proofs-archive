
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive134
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_134 :
    coefficientPositivePacketTerms134 =
      (positiveEdgeTerms.drop 77184).take 576 := by
  unfold coefficientPositivePacketTerms134 coefficientPositivePacketRows134
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
