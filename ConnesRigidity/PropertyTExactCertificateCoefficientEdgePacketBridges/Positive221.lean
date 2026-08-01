


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive221
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_221 :
    coefficientPositivePacketTerms221 =
      (positiveEdgeTerms.drop 127296).take 576 := by
  unfold coefficientPositivePacketTerms221 coefficientPositivePacketRows221
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
