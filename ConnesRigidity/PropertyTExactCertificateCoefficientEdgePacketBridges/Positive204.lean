


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive204
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_204 :
    coefficientPositivePacketTerms204 =
      (positiveEdgeTerms.drop 117504).take 576 := by
  unfold coefficientPositivePacketTerms204 coefficientPositivePacketRows204
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
