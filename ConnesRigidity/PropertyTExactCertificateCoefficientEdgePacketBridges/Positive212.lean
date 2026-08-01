


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Positive212
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientPositivePacketTermsBridge_212 :
    coefficientPositivePacketTerms212 =
      (positiveEdgeTerms.drop 122112).take 576 := by
  unfold coefficientPositivePacketTerms212 coefficientPositivePacketRows212
  unfold coefficientPositivePacketsTerms
  unfold coefficientPositivePacketTerms
    decodeCoefficientPositivePacket
    coefficientPositiveDecodedPacketTerms coefficientEdgeTerm
  unfold positiveEdgeTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
