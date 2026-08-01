


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive239
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_239 :
    coefficientPositivePacketTerms239 =
      (positiveEdgeTerms.drop 137664).take 576 := by
  unfold coefficientPositivePacketTerms239 coefficientPositivePacketRows239
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
