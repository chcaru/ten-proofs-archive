


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive171
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_171 :
    coefficientPositivePacketTerms171 =
      (positiveEdgeTerms.drop 98496).take 576 := by
  unfold coefficientPositivePacketTerms171 coefficientPositivePacketRows171
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
