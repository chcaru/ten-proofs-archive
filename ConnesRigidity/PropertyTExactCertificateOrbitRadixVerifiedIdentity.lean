
import ConnesRigidity.PropertyTExactCertificateOrbitRadixDenseVerified
import ConnesRigidity.PropertyTExactCertificateOrbitRadixGramRecordBridge

namespace ConnesRigidity.AffineSymplecticOrbitCertificate

theorem orbitRadixGramRecordValue_eq_reducedGramEncoding (row : Fin 424) :
    orbitRadixRecordValue radixEncodedGramData row.val =
      orbitRadixReducedGramEncoding row.val :=
  orbitRadixGramRecordValue_eq_reducedGramEncoding_of_dense row
    (orbitRadixDenseReducedGramRow_eq row)

theorem orbitRadix_packed_identity (row : Fin 424) :
    orbitRadixEncode
        ((List.finRange 424).map (orbitRadixComputedEntry row)) =
      congruenceInverseScale ^ 2 *
        orbitRadixEncode
          ((List.finRange 424).map fun column =>
            gramEntry (row.val + 1) (column.val + 1)) :=
  orbitRadix_packed_identity_of_verified_dense
    orbitRadixDenseReducedGramRow_eq row

theorem orbitRadix_integer_identity (row column : Fin 424) :
    orbitRadixComputedEntry row column =
      congruenceInverseScale ^ 2 *
        gramEntry (row.val + 1) (column.val + 1) :=
  orbitRadix_integer_identity_of_verified_dense
    orbitRadixDenseReducedGramRow_eq row column

end ConnesRigidity.AffineSymplecticOrbitCertificate
