


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive065
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_065 :
    coefficientPositivePacketTerms065 =
      (positiveEdgeTerms.drop 37440).take 576 := by
  unfold coefficientPositivePacketTerms065 coefficientPositivePacketRows065
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
