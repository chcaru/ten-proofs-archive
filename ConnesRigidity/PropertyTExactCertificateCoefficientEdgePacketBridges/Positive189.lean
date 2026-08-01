


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive189
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_189 :
    coefficientPositivePacketTerms189 =
      (positiveEdgeTerms.drop 108864).take 576 := by
  unfold coefficientPositivePacketTerms189 coefficientPositivePacketRows189
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
