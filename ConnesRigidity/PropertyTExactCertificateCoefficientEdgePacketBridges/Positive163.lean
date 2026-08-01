
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive163
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_163 :
    coefficientPositivePacketTerms163 =
      (positiveEdgeTerms.drop 93888).take 576 := by
  unfold coefficientPositivePacketTerms163 coefficientPositivePacketRows163
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
