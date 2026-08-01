


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive211
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_211 :
    coefficientPositivePacketTerms211 =
      (positiveEdgeTerms.drop 121536).take 576 := by
  unfold coefficientPositivePacketTerms211 coefficientPositivePacketRows211
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
