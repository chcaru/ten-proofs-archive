


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive175
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_175 :
    coefficientPositivePacketTerms175 =
      (positiveEdgeTerms.drop 100800).take 576 := by
  unfold coefficientPositivePacketTerms175 coefficientPositivePacketRows175
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
