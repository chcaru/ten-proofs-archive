


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal005
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_005 :
    coefficientDiagonalPacketTerms005 =
      (diagonalTerms.drop 1280).take 256 := by
  unfold coefficientDiagonalPacketTerms005 coefficientDiagonalPacketRows005
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
