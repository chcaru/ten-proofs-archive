


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive173
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_173 :
    coefficientPositivePacketTerms173 =
      (positiveEdgeTerms.drop 99648).take 576 := by
  unfold coefficientPositivePacketTerms173 coefficientPositivePacketRows173
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
