
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive040
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_040 :
    coefficientPositivePacketTerms040 =
      (positiveEdgeTerms.drop 23040).take 576 := by
  unfold coefficientPositivePacketTerms040 coefficientPositivePacketRows040
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
