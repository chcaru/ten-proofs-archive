


import ConnesRigidity.PropertyTExactCertificateCoefficientLeaves
import ConnesRigidity.PropertyTExactCertificateCoefficientTarget
import Mathlib.Tactic.FinCases





namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

theorem allCoefficientEncodingLeafChecks (leaf : Fin 82) :
    coefficientCheckData (coefficientSourceChunk leaf) =
      (coefficientSourceEncodingRows.getD leaf #[],
        coefficientSourceAbsoluteTotals.getD leaf 0) := by
  fin_cases leaf
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_000
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_001
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_002
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_003
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_004
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_005
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_006
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_007
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_008
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_009
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_010
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_011
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_012
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_013
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_014
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_015
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_016
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_017
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_018
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_019
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_020
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_021
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_022
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_023
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_024
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_025
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_026
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_027
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_028
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_029
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_030
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_031
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_032
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_033
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_034
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_035
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_036
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_037
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_038
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_039
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_040
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_041
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_042
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_043
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_044
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_045
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_046
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_047
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_048
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_049
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_050
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_051
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_052
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_053
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_054
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_055
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_056
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_057
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_058
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_059
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_060
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_061
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_062
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_063
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_064
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_065
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_066
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_067
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_068
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_069
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_070
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_071
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_072
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_073
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_074
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_075
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_076
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_077
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_078
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_079
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_080
  · simpa [coefficientSourceChunk, coefficientSourceChunks,
      coefficientFactorTermChunks, coefficientSourceEncodingRows,
      coefficientSourceAbsoluteTotals] using
        coefficientEncodingLeafCheck_081

set_option maxHeartbeats 0 in

theorem coefficientEncodingAggregateCheck :
    sumCoefficientEncodingRows coefficientSourceEncodingRows =
        coefficientTargetEncoding ∧
      coefficientSourceAbsoluteTotals.sum +
          18435840000000000 <
        18446744073709551616 := by
  unfold sumCoefficientEncodingRows addCoefficientEncodingRows
    coefficientSourceEncodingRows coefficientSourceAbsoluteTotals
    coefficientTargetEncoding
    coefficientSourceEncoding_000
    coefficientSourceEncoding_001
    coefficientSourceEncoding_002
    coefficientSourceEncoding_003
    coefficientSourceEncoding_004
    coefficientSourceEncoding_005
    coefficientSourceEncoding_006
    coefficientSourceEncoding_007
    coefficientSourceEncoding_008
    coefficientSourceEncoding_009
    coefficientSourceEncoding_010
    coefficientSourceEncoding_011
    coefficientSourceEncoding_012
    coefficientSourceEncoding_013
    coefficientSourceEncoding_014
    coefficientSourceEncoding_015
    coefficientSourceEncoding_016
    coefficientSourceEncoding_017
    coefficientSourceEncoding_018
    coefficientSourceEncoding_019
    coefficientSourceEncoding_020
    coefficientSourceEncoding_021
    coefficientSourceEncoding_022
    coefficientSourceEncoding_023
    coefficientSourceEncoding_024
    coefficientSourceEncoding_025
    coefficientSourceEncoding_026
    coefficientSourceEncoding_027
    coefficientSourceEncoding_028
    coefficientSourceEncoding_029
    coefficientSourceEncoding_030
    coefficientSourceEncoding_031
    coefficientSourceEncoding_032
    coefficientSourceEncoding_033
    coefficientSourceEncoding_034
    coefficientSourceEncoding_035
    coefficientSourceEncoding_036
    coefficientSourceEncoding_037
    coefficientSourceEncoding_038
    coefficientSourceEncoding_039
    coefficientSourceEncoding_040
    coefficientSourceEncoding_041
    coefficientSourceEncoding_042
    coefficientSourceEncoding_043
    coefficientSourceEncoding_044
    coefficientSourceEncoding_045
    coefficientSourceEncoding_046
    coefficientSourceEncoding_047
    coefficientSourceEncoding_048
    coefficientSourceEncoding_049
    coefficientSourceEncoding_050
    coefficientSourceEncoding_051
    coefficientSourceEncoding_052
    coefficientSourceEncoding_053
    coefficientSourceEncoding_054
    coefficientSourceEncoding_055
    coefficientSourceEncoding_056
    coefficientSourceEncoding_057
    coefficientSourceEncoding_058
    coefficientSourceEncoding_059
    coefficientSourceEncoding_060
    coefficientSourceEncoding_061
    coefficientSourceEncoding_062
    coefficientSourceEncoding_063
    coefficientSourceEncoding_064
    coefficientSourceEncoding_065
    coefficientSourceEncoding_066
    coefficientSourceEncoding_067
    coefficientSourceEncoding_068
    coefficientSourceEncoding_069
    coefficientSourceEncoding_070
    coefficientSourceEncoding_071
    coefficientSourceEncoding_072
    coefficientSourceEncoding_073
    coefficientSourceEncoding_074
    coefficientSourceEncoding_075
    coefficientSourceEncoding_076
    coefficientSourceEncoding_077
    coefficientSourceEncoding_078
    coefficientSourceEncoding_079
    coefficientSourceEncoding_080
    coefficientSourceEncoding_081
  decide +kernel

end AffineSymplecticCertificate

end ConnesRigidity
