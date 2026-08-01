


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive249
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_249 :
    coefficientPositivePacketTerms249 =
      (positiveEdgeTerms.drop 143424).take 576 := by
  unfold coefficientPositivePacketTerms249 coefficientPositivePacketRows249
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
