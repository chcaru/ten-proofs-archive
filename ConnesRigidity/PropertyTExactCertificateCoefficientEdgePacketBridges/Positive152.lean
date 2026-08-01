


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive152
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_152 :
    coefficientPositivePacketTerms152 =
      (positiveEdgeTerms.drop 87552).take 576 := by
  unfold coefficientPositivePacketTerms152 coefficientPositivePacketRows152
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
