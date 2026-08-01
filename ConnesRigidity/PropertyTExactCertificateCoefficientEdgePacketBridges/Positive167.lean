
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive167
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_167 :
    coefficientPositivePacketTerms167 =
      (positiveEdgeTerms.drop 96192).take 576 := by
  unfold coefficientPositivePacketTerms167 coefficientPositivePacketRows167
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
