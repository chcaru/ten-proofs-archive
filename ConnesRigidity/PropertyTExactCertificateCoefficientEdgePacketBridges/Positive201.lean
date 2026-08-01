


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive201
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_201 :
    coefficientPositivePacketTerms201 =
      (positiveEdgeTerms.drop 115776).take 576 := by
  unfold coefficientPositivePacketTerms201 coefficientPositivePacketRows201
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
