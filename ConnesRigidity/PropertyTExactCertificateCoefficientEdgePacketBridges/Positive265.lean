


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive265
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_265 :
    coefficientPositivePacketTerms265 =
      (positiveEdgeTerms.drop 152640).take 576 := by
  unfold coefficientPositivePacketTerms265 coefficientPositivePacketRows265
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
