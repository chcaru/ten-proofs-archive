


import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal006
import ConnesRigidity.PropertyTExactCertificateTerms







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
theorem coefficientDiagonalPacketTermsBridge_006 :
    coefficientDiagonalPacketTerms006 =
      (diagonalTerms.drop 1536).take 160 := by
  unfold coefficientDiagonalPacketTerms006 coefficientDiagonalPacketRows006
  unfold coefficientDiagonalPacketsTerms
  unfold coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  unfold diagonalTerms
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
