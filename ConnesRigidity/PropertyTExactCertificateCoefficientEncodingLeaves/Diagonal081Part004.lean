


import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import ConnesRigidity.PropertyTExactCertificateCoefficientEdgePackets.Diagonal004
import ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part004.Entry000







namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

@[irreducible] noncomputable def coefficientSourceEncoding_081_004 :
    Array Int :=
  (ConnesRigidity.CertificateLiterals.PropertyTExactCertificateCoefficientEncodingLeaves.Diagonal081Part004.Entry000.data).getD 0 #[]

set_option maxHeartbeats 0 in

theorem coefficientEncodingDiagonal081PartCheck_004 :
    coefficientCheckData coefficientDiagonalPacketTerms004 =
      (coefficientSourceEncoding_081_004, 10171471222528) := by
  unfold coefficientCheckData coefficientSourceEncoding_081_004
  unfold coefficientDiagonalPacketTerms004 coefficientDiagonalPacketRows004
  unfold coefficientDiagonalPacketsTerms coefficientDiagonalPacketTerms
    decodeCoefficientDiagonalPacket
    coefficientDiagonalDecodedPacketTerms coefficientEdgeTerm
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
