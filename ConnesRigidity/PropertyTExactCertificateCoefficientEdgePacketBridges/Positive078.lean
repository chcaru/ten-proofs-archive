
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive078
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_078 :
    coefficientPositivePacketTerms078 =
      (positiveEdgeTerms.drop 44928).take 576 := by
  unfold coefficientPositivePacketTerms078 coefficientPositivePacketRows078
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
