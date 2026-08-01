


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive219
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_219 :
    coefficientPositivePacketTerms219 =
      (positiveEdgeTerms.drop 126144).take 576 := by
  unfold coefficientPositivePacketTerms219 coefficientPositivePacketRows219
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
