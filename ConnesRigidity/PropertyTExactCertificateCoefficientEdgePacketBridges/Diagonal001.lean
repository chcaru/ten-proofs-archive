
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal001
import ConnesRigidity.PropertyTExactCertificateTerms

namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_001 :
    coefficientDiagonalPacketTerms001 =
      (diagonalTerms.drop 256).take 256 := by
  unfold coefficientDiagonalPacketTerms001 coefficientDiagonalPacketRows001
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
