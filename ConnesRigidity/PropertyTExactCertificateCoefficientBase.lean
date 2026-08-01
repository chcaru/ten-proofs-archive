


import ConnesRigidity.PropertyTExactCertificateCoefficientChecker
import ConnesRigidity.PropertyTExactCertificateTerms
import Mathlib.Data.List.SplitLengths








namespace ConnesRigidity

namespace AffineSymplecticCertificate

set_option maxRecDepth 1000000

noncomputable def coefficientFactorTermRowData
    (productRow gramRow : Array Int) :
    List (IntegerTableTerm 73033) :=
  List.zipWith
    (fun productIndex gramCoefficient =>
      coefficientTerm productIndex.toNat
        (8 * gramCoefficient))
    productRow.toList gramRow.toList


@[irreducible] noncomputable def coefficientFactorTermChunk000 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow000
      coefficientFullGramDataRow000,
    coefficientFactorTermRowData productIndexDataRow001
      coefficientFullGramDataRow001,
    coefficientFactorTermRowData productIndexDataRow002
      coefficientFullGramDataRow002,
    coefficientFactorTermRowData productIndexDataRow003
      coefficientFullGramDataRow003,
    coefficientFactorTermRowData productIndexDataRow004
      coefficientFullGramDataRow004,
    coefficientFactorTermRowData productIndexDataRow005
      coefficientFullGramDataRow005,
    coefficientFactorTermRowData productIndexDataRow006
      coefficientFullGramDataRow006,
    coefficientFactorTermRowData productIndexDataRow007
      coefficientFullGramDataRow007,
    coefficientFactorTermRowData productIndexDataRow008
      coefficientFullGramDataRow008,
    coefficientFactorTermRowData productIndexDataRow009
      coefficientFullGramDataRow009]

@[irreducible] noncomputable def coefficientFactorTermChunk001 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow010
      coefficientFullGramDataRow010,
    coefficientFactorTermRowData productIndexDataRow011
      coefficientFullGramDataRow011,
    coefficientFactorTermRowData productIndexDataRow012
      coefficientFullGramDataRow012,
    coefficientFactorTermRowData productIndexDataRow013
      coefficientFullGramDataRow013,
    coefficientFactorTermRowData productIndexDataRow014
      coefficientFullGramDataRow014,
    coefficientFactorTermRowData productIndexDataRow015
      coefficientFullGramDataRow015,
    coefficientFactorTermRowData productIndexDataRow016
      coefficientFullGramDataRow016,
    coefficientFactorTermRowData productIndexDataRow017
      coefficientFullGramDataRow017,
    coefficientFactorTermRowData productIndexDataRow018
      coefficientFullGramDataRow018,
    coefficientFactorTermRowData productIndexDataRow019
      coefficientFullGramDataRow019]

@[irreducible] noncomputable def coefficientFactorTermChunk002 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow020
      coefficientFullGramDataRow020,
    coefficientFactorTermRowData productIndexDataRow021
      coefficientFullGramDataRow021,
    coefficientFactorTermRowData productIndexDataRow022
      coefficientFullGramDataRow022,
    coefficientFactorTermRowData productIndexDataRow023
      coefficientFullGramDataRow023,
    coefficientFactorTermRowData productIndexDataRow024
      coefficientFullGramDataRow024,
    coefficientFactorTermRowData productIndexDataRow025
      coefficientFullGramDataRow025,
    coefficientFactorTermRowData productIndexDataRow026
      coefficientFullGramDataRow026,
    coefficientFactorTermRowData productIndexDataRow027
      coefficientFullGramDataRow027,
    coefficientFactorTermRowData productIndexDataRow028
      coefficientFullGramDataRow028,
    coefficientFactorTermRowData productIndexDataRow029
      coefficientFullGramDataRow029]

@[irreducible] noncomputable def coefficientFactorTermChunk003 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow030
      coefficientFullGramDataRow030,
    coefficientFactorTermRowData productIndexDataRow031
      coefficientFullGramDataRow031,
    coefficientFactorTermRowData productIndexDataRow032
      coefficientFullGramDataRow032,
    coefficientFactorTermRowData productIndexDataRow033
      coefficientFullGramDataRow033,
    coefficientFactorTermRowData productIndexDataRow034
      coefficientFullGramDataRow034,
    coefficientFactorTermRowData productIndexDataRow035
      coefficientFullGramDataRow035,
    coefficientFactorTermRowData productIndexDataRow036
      coefficientFullGramDataRow036,
    coefficientFactorTermRowData productIndexDataRow037
      coefficientFullGramDataRow037,
    coefficientFactorTermRowData productIndexDataRow038
      coefficientFullGramDataRow038,
    coefficientFactorTermRowData productIndexDataRow039
      coefficientFullGramDataRow039]

@[irreducible] noncomputable def coefficientFactorTermChunk004 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow040
      coefficientFullGramDataRow040,
    coefficientFactorTermRowData productIndexDataRow041
      coefficientFullGramDataRow041,
    coefficientFactorTermRowData productIndexDataRow042
      coefficientFullGramDataRow042,
    coefficientFactorTermRowData productIndexDataRow043
      coefficientFullGramDataRow043,
    coefficientFactorTermRowData productIndexDataRow044
      coefficientFullGramDataRow044,
    coefficientFactorTermRowData productIndexDataRow045
      coefficientFullGramDataRow045,
    coefficientFactorTermRowData productIndexDataRow046
      coefficientFullGramDataRow046,
    coefficientFactorTermRowData productIndexDataRow047
      coefficientFullGramDataRow047,
    coefficientFactorTermRowData productIndexDataRow048
      coefficientFullGramDataRow048,
    coefficientFactorTermRowData productIndexDataRow049
      coefficientFullGramDataRow049]

@[irreducible] noncomputable def coefficientFactorTermChunk005 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow050
      coefficientFullGramDataRow050,
    coefficientFactorTermRowData productIndexDataRow051
      coefficientFullGramDataRow051,
    coefficientFactorTermRowData productIndexDataRow052
      coefficientFullGramDataRow052,
    coefficientFactorTermRowData productIndexDataRow053
      coefficientFullGramDataRow053,
    coefficientFactorTermRowData productIndexDataRow054
      coefficientFullGramDataRow054,
    coefficientFactorTermRowData productIndexDataRow055
      coefficientFullGramDataRow055,
    coefficientFactorTermRowData productIndexDataRow056
      coefficientFullGramDataRow056,
    coefficientFactorTermRowData productIndexDataRow057
      coefficientFullGramDataRow057,
    coefficientFactorTermRowData productIndexDataRow058
      coefficientFullGramDataRow058,
    coefficientFactorTermRowData productIndexDataRow059
      coefficientFullGramDataRow059]

@[irreducible] noncomputable def coefficientFactorTermChunk006 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow060
      coefficientFullGramDataRow060,
    coefficientFactorTermRowData productIndexDataRow061
      coefficientFullGramDataRow061,
    coefficientFactorTermRowData productIndexDataRow062
      coefficientFullGramDataRow062,
    coefficientFactorTermRowData productIndexDataRow063
      coefficientFullGramDataRow063,
    coefficientFactorTermRowData productIndexDataRow064
      coefficientFullGramDataRow064,
    coefficientFactorTermRowData productIndexDataRow065
      coefficientFullGramDataRow065,
    coefficientFactorTermRowData productIndexDataRow066
      coefficientFullGramDataRow066,
    coefficientFactorTermRowData productIndexDataRow067
      coefficientFullGramDataRow067,
    coefficientFactorTermRowData productIndexDataRow068
      coefficientFullGramDataRow068,
    coefficientFactorTermRowData productIndexDataRow069
      coefficientFullGramDataRow069]

@[irreducible] noncomputable def coefficientFactorTermChunk007 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow070
      coefficientFullGramDataRow070,
    coefficientFactorTermRowData productIndexDataRow071
      coefficientFullGramDataRow071,
    coefficientFactorTermRowData productIndexDataRow072
      coefficientFullGramDataRow072,
    coefficientFactorTermRowData productIndexDataRow073
      coefficientFullGramDataRow073,
    coefficientFactorTermRowData productIndexDataRow074
      coefficientFullGramDataRow074,
    coefficientFactorTermRowData productIndexDataRow075
      coefficientFullGramDataRow075,
    coefficientFactorTermRowData productIndexDataRow076
      coefficientFullGramDataRow076,
    coefficientFactorTermRowData productIndexDataRow077
      coefficientFullGramDataRow077,
    coefficientFactorTermRowData productIndexDataRow078
      coefficientFullGramDataRow078,
    coefficientFactorTermRowData productIndexDataRow079
      coefficientFullGramDataRow079]

@[irreducible] noncomputable def coefficientFactorTermChunk008 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow080
      coefficientFullGramDataRow080,
    coefficientFactorTermRowData productIndexDataRow081
      coefficientFullGramDataRow081,
    coefficientFactorTermRowData productIndexDataRow082
      coefficientFullGramDataRow082,
    coefficientFactorTermRowData productIndexDataRow083
      coefficientFullGramDataRow083,
    coefficientFactorTermRowData productIndexDataRow084
      coefficientFullGramDataRow084,
    coefficientFactorTermRowData productIndexDataRow085
      coefficientFullGramDataRow085,
    coefficientFactorTermRowData productIndexDataRow086
      coefficientFullGramDataRow086,
    coefficientFactorTermRowData productIndexDataRow087
      coefficientFullGramDataRow087,
    coefficientFactorTermRowData productIndexDataRow088
      coefficientFullGramDataRow088,
    coefficientFactorTermRowData productIndexDataRow089
      coefficientFullGramDataRow089]

@[irreducible] noncomputable def coefficientFactorTermChunk009 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow090
      coefficientFullGramDataRow090,
    coefficientFactorTermRowData productIndexDataRow091
      coefficientFullGramDataRow091,
    coefficientFactorTermRowData productIndexDataRow092
      coefficientFullGramDataRow092,
    coefficientFactorTermRowData productIndexDataRow093
      coefficientFullGramDataRow093,
    coefficientFactorTermRowData productIndexDataRow094
      coefficientFullGramDataRow094,
    coefficientFactorTermRowData productIndexDataRow095
      coefficientFullGramDataRow095,
    coefficientFactorTermRowData productIndexDataRow096
      coefficientFullGramDataRow096,
    coefficientFactorTermRowData productIndexDataRow097
      coefficientFullGramDataRow097,
    coefficientFactorTermRowData productIndexDataRow098
      coefficientFullGramDataRow098,
    coefficientFactorTermRowData productIndexDataRow099
      coefficientFullGramDataRow099]

@[irreducible] noncomputable def coefficientFactorTermChunk010 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow100
      coefficientFullGramDataRow100,
    coefficientFactorTermRowData productIndexDataRow101
      coefficientFullGramDataRow101,
    coefficientFactorTermRowData productIndexDataRow102
      coefficientFullGramDataRow102,
    coefficientFactorTermRowData productIndexDataRow103
      coefficientFullGramDataRow103,
    coefficientFactorTermRowData productIndexDataRow104
      coefficientFullGramDataRow104,
    coefficientFactorTermRowData productIndexDataRow105
      coefficientFullGramDataRow105,
    coefficientFactorTermRowData productIndexDataRow106
      coefficientFullGramDataRow106,
    coefficientFactorTermRowData productIndexDataRow107
      coefficientFullGramDataRow107,
    coefficientFactorTermRowData productIndexDataRow108
      coefficientFullGramDataRow108,
    coefficientFactorTermRowData productIndexDataRow109
      coefficientFullGramDataRow109]

@[irreducible] noncomputable def coefficientFactorTermChunk011 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow110
      coefficientFullGramDataRow110,
    coefficientFactorTermRowData productIndexDataRow111
      coefficientFullGramDataRow111,
    coefficientFactorTermRowData productIndexDataRow112
      coefficientFullGramDataRow112,
    coefficientFactorTermRowData productIndexDataRow113
      coefficientFullGramDataRow113,
    coefficientFactorTermRowData productIndexDataRow114
      coefficientFullGramDataRow114,
    coefficientFactorTermRowData productIndexDataRow115
      coefficientFullGramDataRow115,
    coefficientFactorTermRowData productIndexDataRow116
      coefficientFullGramDataRow116,
    coefficientFactorTermRowData productIndexDataRow117
      coefficientFullGramDataRow117,
    coefficientFactorTermRowData productIndexDataRow118
      coefficientFullGramDataRow118,
    coefficientFactorTermRowData productIndexDataRow119
      coefficientFullGramDataRow119]

@[irreducible] noncomputable def coefficientFactorTermChunk012 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow120
      coefficientFullGramDataRow120,
    coefficientFactorTermRowData productIndexDataRow121
      coefficientFullGramDataRow121,
    coefficientFactorTermRowData productIndexDataRow122
      coefficientFullGramDataRow122,
    coefficientFactorTermRowData productIndexDataRow123
      coefficientFullGramDataRow123,
    coefficientFactorTermRowData productIndexDataRow124
      coefficientFullGramDataRow124,
    coefficientFactorTermRowData productIndexDataRow125
      coefficientFullGramDataRow125,
    coefficientFactorTermRowData productIndexDataRow126
      coefficientFullGramDataRow126,
    coefficientFactorTermRowData productIndexDataRow127
      coefficientFullGramDataRow127,
    coefficientFactorTermRowData productIndexDataRow128
      coefficientFullGramDataRow128,
    coefficientFactorTermRowData productIndexDataRow129
      coefficientFullGramDataRow129]

@[irreducible] noncomputable def coefficientFactorTermChunk013 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow130
      coefficientFullGramDataRow130,
    coefficientFactorTermRowData productIndexDataRow131
      coefficientFullGramDataRow131,
    coefficientFactorTermRowData productIndexDataRow132
      coefficientFullGramDataRow132,
    coefficientFactorTermRowData productIndexDataRow133
      coefficientFullGramDataRow133,
    coefficientFactorTermRowData productIndexDataRow134
      coefficientFullGramDataRow134,
    coefficientFactorTermRowData productIndexDataRow135
      coefficientFullGramDataRow135,
    coefficientFactorTermRowData productIndexDataRow136
      coefficientFullGramDataRow136,
    coefficientFactorTermRowData productIndexDataRow137
      coefficientFullGramDataRow137,
    coefficientFactorTermRowData productIndexDataRow138
      coefficientFullGramDataRow138,
    coefficientFactorTermRowData productIndexDataRow139
      coefficientFullGramDataRow139]

@[irreducible] noncomputable def coefficientFactorTermChunk014 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow140
      coefficientFullGramDataRow140,
    coefficientFactorTermRowData productIndexDataRow141
      coefficientFullGramDataRow141,
    coefficientFactorTermRowData productIndexDataRow142
      coefficientFullGramDataRow142,
    coefficientFactorTermRowData productIndexDataRow143
      coefficientFullGramDataRow143,
    coefficientFactorTermRowData productIndexDataRow144
      coefficientFullGramDataRow144,
    coefficientFactorTermRowData productIndexDataRow145
      coefficientFullGramDataRow145,
    coefficientFactorTermRowData productIndexDataRow146
      coefficientFullGramDataRow146,
    coefficientFactorTermRowData productIndexDataRow147
      coefficientFullGramDataRow147,
    coefficientFactorTermRowData productIndexDataRow148
      coefficientFullGramDataRow148,
    coefficientFactorTermRowData productIndexDataRow149
      coefficientFullGramDataRow149]

@[irreducible] noncomputable def coefficientFactorTermChunk015 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow150
      coefficientFullGramDataRow150,
    coefficientFactorTermRowData productIndexDataRow151
      coefficientFullGramDataRow151,
    coefficientFactorTermRowData productIndexDataRow152
      coefficientFullGramDataRow152,
    coefficientFactorTermRowData productIndexDataRow153
      coefficientFullGramDataRow153,
    coefficientFactorTermRowData productIndexDataRow154
      coefficientFullGramDataRow154,
    coefficientFactorTermRowData productIndexDataRow155
      coefficientFullGramDataRow155,
    coefficientFactorTermRowData productIndexDataRow156
      coefficientFullGramDataRow156,
    coefficientFactorTermRowData productIndexDataRow157
      coefficientFullGramDataRow157,
    coefficientFactorTermRowData productIndexDataRow158
      coefficientFullGramDataRow158,
    coefficientFactorTermRowData productIndexDataRow159
      coefficientFullGramDataRow159]

@[irreducible] noncomputable def coefficientFactorTermChunk016 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow160
      coefficientFullGramDataRow160,
    coefficientFactorTermRowData productIndexDataRow161
      coefficientFullGramDataRow161,
    coefficientFactorTermRowData productIndexDataRow162
      coefficientFullGramDataRow162,
    coefficientFactorTermRowData productIndexDataRow163
      coefficientFullGramDataRow163,
    coefficientFactorTermRowData productIndexDataRow164
      coefficientFullGramDataRow164,
    coefficientFactorTermRowData productIndexDataRow165
      coefficientFullGramDataRow165,
    coefficientFactorTermRowData productIndexDataRow166
      coefficientFullGramDataRow166,
    coefficientFactorTermRowData productIndexDataRow167
      coefficientFullGramDataRow167,
    coefficientFactorTermRowData productIndexDataRow168
      coefficientFullGramDataRow168,
    coefficientFactorTermRowData productIndexDataRow169
      coefficientFullGramDataRow169]

@[irreducible] noncomputable def coefficientFactorTermChunk017 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow170
      coefficientFullGramDataRow170,
    coefficientFactorTermRowData productIndexDataRow171
      coefficientFullGramDataRow171,
    coefficientFactorTermRowData productIndexDataRow172
      coefficientFullGramDataRow172,
    coefficientFactorTermRowData productIndexDataRow173
      coefficientFullGramDataRow173,
    coefficientFactorTermRowData productIndexDataRow174
      coefficientFullGramDataRow174,
    coefficientFactorTermRowData productIndexDataRow175
      coefficientFullGramDataRow175,
    coefficientFactorTermRowData productIndexDataRow176
      coefficientFullGramDataRow176,
    coefficientFactorTermRowData productIndexDataRow177
      coefficientFullGramDataRow177,
    coefficientFactorTermRowData productIndexDataRow178
      coefficientFullGramDataRow178,
    coefficientFactorTermRowData productIndexDataRow179
      coefficientFullGramDataRow179]

@[irreducible] noncomputable def coefficientFactorTermChunk018 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow180
      coefficientFullGramDataRow180,
    coefficientFactorTermRowData productIndexDataRow181
      coefficientFullGramDataRow181,
    coefficientFactorTermRowData productIndexDataRow182
      coefficientFullGramDataRow182,
    coefficientFactorTermRowData productIndexDataRow183
      coefficientFullGramDataRow183,
    coefficientFactorTermRowData productIndexDataRow184
      coefficientFullGramDataRow184,
    coefficientFactorTermRowData productIndexDataRow185
      coefficientFullGramDataRow185,
    coefficientFactorTermRowData productIndexDataRow186
      coefficientFullGramDataRow186,
    coefficientFactorTermRowData productIndexDataRow187
      coefficientFullGramDataRow187,
    coefficientFactorTermRowData productIndexDataRow188
      coefficientFullGramDataRow188,
    coefficientFactorTermRowData productIndexDataRow189
      coefficientFullGramDataRow189]

@[irreducible] noncomputable def coefficientFactorTermChunk019 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow190
      coefficientFullGramDataRow190,
    coefficientFactorTermRowData productIndexDataRow191
      coefficientFullGramDataRow191,
    coefficientFactorTermRowData productIndexDataRow192
      coefficientFullGramDataRow192,
    coefficientFactorTermRowData productIndexDataRow193
      coefficientFullGramDataRow193,
    coefficientFactorTermRowData productIndexDataRow194
      coefficientFullGramDataRow194,
    coefficientFactorTermRowData productIndexDataRow195
      coefficientFullGramDataRow195,
    coefficientFactorTermRowData productIndexDataRow196
      coefficientFullGramDataRow196,
    coefficientFactorTermRowData productIndexDataRow197
      coefficientFullGramDataRow197,
    coefficientFactorTermRowData productIndexDataRow198
      coefficientFullGramDataRow198,
    coefficientFactorTermRowData productIndexDataRow199
      coefficientFullGramDataRow199]

@[irreducible] noncomputable def coefficientFactorTermChunk020 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow200
      coefficientFullGramDataRow200,
    coefficientFactorTermRowData productIndexDataRow201
      coefficientFullGramDataRow201,
    coefficientFactorTermRowData productIndexDataRow202
      coefficientFullGramDataRow202,
    coefficientFactorTermRowData productIndexDataRow203
      coefficientFullGramDataRow203,
    coefficientFactorTermRowData productIndexDataRow204
      coefficientFullGramDataRow204,
    coefficientFactorTermRowData productIndexDataRow205
      coefficientFullGramDataRow205,
    coefficientFactorTermRowData productIndexDataRow206
      coefficientFullGramDataRow206,
    coefficientFactorTermRowData productIndexDataRow207
      coefficientFullGramDataRow207,
    coefficientFactorTermRowData productIndexDataRow208
      coefficientFullGramDataRow208,
    coefficientFactorTermRowData productIndexDataRow209
      coefficientFullGramDataRow209]

@[irreducible] noncomputable def coefficientFactorTermChunk021 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow210
      coefficientFullGramDataRow210,
    coefficientFactorTermRowData productIndexDataRow211
      coefficientFullGramDataRow211,
    coefficientFactorTermRowData productIndexDataRow212
      coefficientFullGramDataRow212,
    coefficientFactorTermRowData productIndexDataRow213
      coefficientFullGramDataRow213,
    coefficientFactorTermRowData productIndexDataRow214
      coefficientFullGramDataRow214,
    coefficientFactorTermRowData productIndexDataRow215
      coefficientFullGramDataRow215,
    coefficientFactorTermRowData productIndexDataRow216
      coefficientFullGramDataRow216,
    coefficientFactorTermRowData productIndexDataRow217
      coefficientFullGramDataRow217,
    coefficientFactorTermRowData productIndexDataRow218
      coefficientFullGramDataRow218,
    coefficientFactorTermRowData productIndexDataRow219
      coefficientFullGramDataRow219]

@[irreducible] noncomputable def coefficientFactorTermChunk022 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow220
      coefficientFullGramDataRow220,
    coefficientFactorTermRowData productIndexDataRow221
      coefficientFullGramDataRow221,
    coefficientFactorTermRowData productIndexDataRow222
      coefficientFullGramDataRow222,
    coefficientFactorTermRowData productIndexDataRow223
      coefficientFullGramDataRow223,
    coefficientFactorTermRowData productIndexDataRow224
      coefficientFullGramDataRow224,
    coefficientFactorTermRowData productIndexDataRow225
      coefficientFullGramDataRow225,
    coefficientFactorTermRowData productIndexDataRow226
      coefficientFullGramDataRow226,
    coefficientFactorTermRowData productIndexDataRow227
      coefficientFullGramDataRow227,
    coefficientFactorTermRowData productIndexDataRow228
      coefficientFullGramDataRow228,
    coefficientFactorTermRowData productIndexDataRow229
      coefficientFullGramDataRow229]

@[irreducible] noncomputable def coefficientFactorTermChunk023 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow230
      coefficientFullGramDataRow230,
    coefficientFactorTermRowData productIndexDataRow231
      coefficientFullGramDataRow231,
    coefficientFactorTermRowData productIndexDataRow232
      coefficientFullGramDataRow232,
    coefficientFactorTermRowData productIndexDataRow233
      coefficientFullGramDataRow233,
    coefficientFactorTermRowData productIndexDataRow234
      coefficientFullGramDataRow234,
    coefficientFactorTermRowData productIndexDataRow235
      coefficientFullGramDataRow235,
    coefficientFactorTermRowData productIndexDataRow236
      coefficientFullGramDataRow236,
    coefficientFactorTermRowData productIndexDataRow237
      coefficientFullGramDataRow237,
    coefficientFactorTermRowData productIndexDataRow238
      coefficientFullGramDataRow238,
    coefficientFactorTermRowData productIndexDataRow239
      coefficientFullGramDataRow239]

@[irreducible] noncomputable def coefficientFactorTermChunk024 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow240
      coefficientFullGramDataRow240,
    coefficientFactorTermRowData productIndexDataRow241
      coefficientFullGramDataRow241,
    coefficientFactorTermRowData productIndexDataRow242
      coefficientFullGramDataRow242,
    coefficientFactorTermRowData productIndexDataRow243
      coefficientFullGramDataRow243,
    coefficientFactorTermRowData productIndexDataRow244
      coefficientFullGramDataRow244,
    coefficientFactorTermRowData productIndexDataRow245
      coefficientFullGramDataRow245,
    coefficientFactorTermRowData productIndexDataRow246
      coefficientFullGramDataRow246,
    coefficientFactorTermRowData productIndexDataRow247
      coefficientFullGramDataRow247,
    coefficientFactorTermRowData productIndexDataRow248
      coefficientFullGramDataRow248,
    coefficientFactorTermRowData productIndexDataRow249
      coefficientFullGramDataRow249]

@[irreducible] noncomputable def coefficientFactorTermChunk025 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow250
      coefficientFullGramDataRow250,
    coefficientFactorTermRowData productIndexDataRow251
      coefficientFullGramDataRow251,
    coefficientFactorTermRowData productIndexDataRow252
      coefficientFullGramDataRow252,
    coefficientFactorTermRowData productIndexDataRow253
      coefficientFullGramDataRow253,
    coefficientFactorTermRowData productIndexDataRow254
      coefficientFullGramDataRow254,
    coefficientFactorTermRowData productIndexDataRow255
      coefficientFullGramDataRow255,
    coefficientFactorTermRowData productIndexDataRow256
      coefficientFullGramDataRow256,
    coefficientFactorTermRowData productIndexDataRow257
      coefficientFullGramDataRow257,
    coefficientFactorTermRowData productIndexDataRow258
      coefficientFullGramDataRow258,
    coefficientFactorTermRowData productIndexDataRow259
      coefficientFullGramDataRow259]

@[irreducible] noncomputable def coefficientFactorTermChunk026 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow260
      coefficientFullGramDataRow260,
    coefficientFactorTermRowData productIndexDataRow261
      coefficientFullGramDataRow261,
    coefficientFactorTermRowData productIndexDataRow262
      coefficientFullGramDataRow262,
    coefficientFactorTermRowData productIndexDataRow263
      coefficientFullGramDataRow263,
    coefficientFactorTermRowData productIndexDataRow264
      coefficientFullGramDataRow264,
    coefficientFactorTermRowData productIndexDataRow265
      coefficientFullGramDataRow265,
    coefficientFactorTermRowData productIndexDataRow266
      coefficientFullGramDataRow266,
    coefficientFactorTermRowData productIndexDataRow267
      coefficientFullGramDataRow267,
    coefficientFactorTermRowData productIndexDataRow268
      coefficientFullGramDataRow268,
    coefficientFactorTermRowData productIndexDataRow269
      coefficientFullGramDataRow269]

@[irreducible] noncomputable def coefficientFactorTermChunk027 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow270
      coefficientFullGramDataRow270,
    coefficientFactorTermRowData productIndexDataRow271
      coefficientFullGramDataRow271,
    coefficientFactorTermRowData productIndexDataRow272
      coefficientFullGramDataRow272,
    coefficientFactorTermRowData productIndexDataRow273
      coefficientFullGramDataRow273,
    coefficientFactorTermRowData productIndexDataRow274
      coefficientFullGramDataRow274,
    coefficientFactorTermRowData productIndexDataRow275
      coefficientFullGramDataRow275,
    coefficientFactorTermRowData productIndexDataRow276
      coefficientFullGramDataRow276,
    coefficientFactorTermRowData productIndexDataRow277
      coefficientFullGramDataRow277,
    coefficientFactorTermRowData productIndexDataRow278
      coefficientFullGramDataRow278,
    coefficientFactorTermRowData productIndexDataRow279
      coefficientFullGramDataRow279]

@[irreducible] noncomputable def coefficientFactorTermChunk028 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow280
      coefficientFullGramDataRow280,
    coefficientFactorTermRowData productIndexDataRow281
      coefficientFullGramDataRow281,
    coefficientFactorTermRowData productIndexDataRow282
      coefficientFullGramDataRow282,
    coefficientFactorTermRowData productIndexDataRow283
      coefficientFullGramDataRow283,
    coefficientFactorTermRowData productIndexDataRow284
      coefficientFullGramDataRow284,
    coefficientFactorTermRowData productIndexDataRow285
      coefficientFullGramDataRow285,
    coefficientFactorTermRowData productIndexDataRow286
      coefficientFullGramDataRow286,
    coefficientFactorTermRowData productIndexDataRow287
      coefficientFullGramDataRow287,
    coefficientFactorTermRowData productIndexDataRow288
      coefficientFullGramDataRow288,
    coefficientFactorTermRowData productIndexDataRow289
      coefficientFullGramDataRow289]

@[irreducible] noncomputable def coefficientFactorTermChunk029 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow290
      coefficientFullGramDataRow290,
    coefficientFactorTermRowData productIndexDataRow291
      coefficientFullGramDataRow291,
    coefficientFactorTermRowData productIndexDataRow292
      coefficientFullGramDataRow292,
    coefficientFactorTermRowData productIndexDataRow293
      coefficientFullGramDataRow293,
    coefficientFactorTermRowData productIndexDataRow294
      coefficientFullGramDataRow294,
    coefficientFactorTermRowData productIndexDataRow295
      coefficientFullGramDataRow295,
    coefficientFactorTermRowData productIndexDataRow296
      coefficientFullGramDataRow296,
    coefficientFactorTermRowData productIndexDataRow297
      coefficientFullGramDataRow297,
    coefficientFactorTermRowData productIndexDataRow298
      coefficientFullGramDataRow298,
    coefficientFactorTermRowData productIndexDataRow299
      coefficientFullGramDataRow299]

@[irreducible] noncomputable def coefficientFactorTermChunk030 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow300
      coefficientFullGramDataRow300,
    coefficientFactorTermRowData productIndexDataRow301
      coefficientFullGramDataRow301,
    coefficientFactorTermRowData productIndexDataRow302
      coefficientFullGramDataRow302,
    coefficientFactorTermRowData productIndexDataRow303
      coefficientFullGramDataRow303,
    coefficientFactorTermRowData productIndexDataRow304
      coefficientFullGramDataRow304,
    coefficientFactorTermRowData productIndexDataRow305
      coefficientFullGramDataRow305,
    coefficientFactorTermRowData productIndexDataRow306
      coefficientFullGramDataRow306,
    coefficientFactorTermRowData productIndexDataRow307
      coefficientFullGramDataRow307,
    coefficientFactorTermRowData productIndexDataRow308
      coefficientFullGramDataRow308,
    coefficientFactorTermRowData productIndexDataRow309
      coefficientFullGramDataRow309]

@[irreducible] noncomputable def coefficientFactorTermChunk031 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow310
      coefficientFullGramDataRow310,
    coefficientFactorTermRowData productIndexDataRow311
      coefficientFullGramDataRow311,
    coefficientFactorTermRowData productIndexDataRow312
      coefficientFullGramDataRow312,
    coefficientFactorTermRowData productIndexDataRow313
      coefficientFullGramDataRow313,
    coefficientFactorTermRowData productIndexDataRow314
      coefficientFullGramDataRow314,
    coefficientFactorTermRowData productIndexDataRow315
      coefficientFullGramDataRow315,
    coefficientFactorTermRowData productIndexDataRow316
      coefficientFullGramDataRow316,
    coefficientFactorTermRowData productIndexDataRow317
      coefficientFullGramDataRow317,
    coefficientFactorTermRowData productIndexDataRow318
      coefficientFullGramDataRow318,
    coefficientFactorTermRowData productIndexDataRow319
      coefficientFullGramDataRow319]

@[irreducible] noncomputable def coefficientFactorTermChunk032 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow320
      coefficientFullGramDataRow320,
    coefficientFactorTermRowData productIndexDataRow321
      coefficientFullGramDataRow321,
    coefficientFactorTermRowData productIndexDataRow322
      coefficientFullGramDataRow322,
    coefficientFactorTermRowData productIndexDataRow323
      coefficientFullGramDataRow323,
    coefficientFactorTermRowData productIndexDataRow324
      coefficientFullGramDataRow324,
    coefficientFactorTermRowData productIndexDataRow325
      coefficientFullGramDataRow325,
    coefficientFactorTermRowData productIndexDataRow326
      coefficientFullGramDataRow326,
    coefficientFactorTermRowData productIndexDataRow327
      coefficientFullGramDataRow327,
    coefficientFactorTermRowData productIndexDataRow328
      coefficientFullGramDataRow328,
    coefficientFactorTermRowData productIndexDataRow329
      coefficientFullGramDataRow329]

@[irreducible] noncomputable def coefficientFactorTermChunk033 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow330
      coefficientFullGramDataRow330,
    coefficientFactorTermRowData productIndexDataRow331
      coefficientFullGramDataRow331,
    coefficientFactorTermRowData productIndexDataRow332
      coefficientFullGramDataRow332,
    coefficientFactorTermRowData productIndexDataRow333
      coefficientFullGramDataRow333,
    coefficientFactorTermRowData productIndexDataRow334
      coefficientFullGramDataRow334,
    coefficientFactorTermRowData productIndexDataRow335
      coefficientFullGramDataRow335,
    coefficientFactorTermRowData productIndexDataRow336
      coefficientFullGramDataRow336,
    coefficientFactorTermRowData productIndexDataRow337
      coefficientFullGramDataRow337,
    coefficientFactorTermRowData productIndexDataRow338
      coefficientFullGramDataRow338,
    coefficientFactorTermRowData productIndexDataRow339
      coefficientFullGramDataRow339]

@[irreducible] noncomputable def coefficientFactorTermChunk034 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow340
      coefficientFullGramDataRow340,
    coefficientFactorTermRowData productIndexDataRow341
      coefficientFullGramDataRow341,
    coefficientFactorTermRowData productIndexDataRow342
      coefficientFullGramDataRow342,
    coefficientFactorTermRowData productIndexDataRow343
      coefficientFullGramDataRow343,
    coefficientFactorTermRowData productIndexDataRow344
      coefficientFullGramDataRow344,
    coefficientFactorTermRowData productIndexDataRow345
      coefficientFullGramDataRow345,
    coefficientFactorTermRowData productIndexDataRow346
      coefficientFullGramDataRow346,
    coefficientFactorTermRowData productIndexDataRow347
      coefficientFullGramDataRow347,
    coefficientFactorTermRowData productIndexDataRow348
      coefficientFullGramDataRow348,
    coefficientFactorTermRowData productIndexDataRow349
      coefficientFullGramDataRow349]

@[irreducible] noncomputable def coefficientFactorTermChunk035 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow350
      coefficientFullGramDataRow350,
    coefficientFactorTermRowData productIndexDataRow351
      coefficientFullGramDataRow351,
    coefficientFactorTermRowData productIndexDataRow352
      coefficientFullGramDataRow352,
    coefficientFactorTermRowData productIndexDataRow353
      coefficientFullGramDataRow353,
    coefficientFactorTermRowData productIndexDataRow354
      coefficientFullGramDataRow354,
    coefficientFactorTermRowData productIndexDataRow355
      coefficientFullGramDataRow355,
    coefficientFactorTermRowData productIndexDataRow356
      coefficientFullGramDataRow356,
    coefficientFactorTermRowData productIndexDataRow357
      coefficientFullGramDataRow357,
    coefficientFactorTermRowData productIndexDataRow358
      coefficientFullGramDataRow358,
    coefficientFactorTermRowData productIndexDataRow359
      coefficientFullGramDataRow359]

@[irreducible] noncomputable def coefficientFactorTermChunk036 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow360
      coefficientFullGramDataRow360,
    coefficientFactorTermRowData productIndexDataRow361
      coefficientFullGramDataRow361,
    coefficientFactorTermRowData productIndexDataRow362
      coefficientFullGramDataRow362,
    coefficientFactorTermRowData productIndexDataRow363
      coefficientFullGramDataRow363,
    coefficientFactorTermRowData productIndexDataRow364
      coefficientFullGramDataRow364,
    coefficientFactorTermRowData productIndexDataRow365
      coefficientFullGramDataRow365,
    coefficientFactorTermRowData productIndexDataRow366
      coefficientFullGramDataRow366,
    coefficientFactorTermRowData productIndexDataRow367
      coefficientFullGramDataRow367,
    coefficientFactorTermRowData productIndexDataRow368
      coefficientFullGramDataRow368,
    coefficientFactorTermRowData productIndexDataRow369
      coefficientFullGramDataRow369]

@[irreducible] noncomputable def coefficientFactorTermChunk037 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow370
      coefficientFullGramDataRow370,
    coefficientFactorTermRowData productIndexDataRow371
      coefficientFullGramDataRow371,
    coefficientFactorTermRowData productIndexDataRow372
      coefficientFullGramDataRow372,
    coefficientFactorTermRowData productIndexDataRow373
      coefficientFullGramDataRow373,
    coefficientFactorTermRowData productIndexDataRow374
      coefficientFullGramDataRow374,
    coefficientFactorTermRowData productIndexDataRow375
      coefficientFullGramDataRow375,
    coefficientFactorTermRowData productIndexDataRow376
      coefficientFullGramDataRow376,
    coefficientFactorTermRowData productIndexDataRow377
      coefficientFullGramDataRow377,
    coefficientFactorTermRowData productIndexDataRow378
      coefficientFullGramDataRow378,
    coefficientFactorTermRowData productIndexDataRow379
      coefficientFullGramDataRow379]

@[irreducible] noncomputable def coefficientFactorTermChunk038 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow380
      coefficientFullGramDataRow380,
    coefficientFactorTermRowData productIndexDataRow381
      coefficientFullGramDataRow381,
    coefficientFactorTermRowData productIndexDataRow382
      coefficientFullGramDataRow382,
    coefficientFactorTermRowData productIndexDataRow383
      coefficientFullGramDataRow383,
    coefficientFactorTermRowData productIndexDataRow384
      coefficientFullGramDataRow384,
    coefficientFactorTermRowData productIndexDataRow385
      coefficientFullGramDataRow385,
    coefficientFactorTermRowData productIndexDataRow386
      coefficientFullGramDataRow386,
    coefficientFactorTermRowData productIndexDataRow387
      coefficientFullGramDataRow387,
    coefficientFactorTermRowData productIndexDataRow388
      coefficientFullGramDataRow388,
    coefficientFactorTermRowData productIndexDataRow389
      coefficientFullGramDataRow389]

@[irreducible] noncomputable def coefficientFactorTermChunk039 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow390
      coefficientFullGramDataRow390,
    coefficientFactorTermRowData productIndexDataRow391
      coefficientFullGramDataRow391,
    coefficientFactorTermRowData productIndexDataRow392
      coefficientFullGramDataRow392,
    coefficientFactorTermRowData productIndexDataRow393
      coefficientFullGramDataRow393,
    coefficientFactorTermRowData productIndexDataRow394
      coefficientFullGramDataRow394,
    coefficientFactorTermRowData productIndexDataRow395
      coefficientFullGramDataRow395,
    coefficientFactorTermRowData productIndexDataRow396
      coefficientFullGramDataRow396,
    coefficientFactorTermRowData productIndexDataRow397
      coefficientFullGramDataRow397,
    coefficientFactorTermRowData productIndexDataRow398
      coefficientFullGramDataRow398,
    coefficientFactorTermRowData productIndexDataRow399
      coefficientFullGramDataRow399]

@[irreducible] noncomputable def coefficientFactorTermChunk040 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow400
      coefficientFullGramDataRow400,
    coefficientFactorTermRowData productIndexDataRow401
      coefficientFullGramDataRow401,
    coefficientFactorTermRowData productIndexDataRow402
      coefficientFullGramDataRow402,
    coefficientFactorTermRowData productIndexDataRow403
      coefficientFullGramDataRow403,
    coefficientFactorTermRowData productIndexDataRow404
      coefficientFullGramDataRow404,
    coefficientFactorTermRowData productIndexDataRow405
      coefficientFullGramDataRow405,
    coefficientFactorTermRowData productIndexDataRow406
      coefficientFullGramDataRow406,
    coefficientFactorTermRowData productIndexDataRow407
      coefficientFullGramDataRow407,
    coefficientFactorTermRowData productIndexDataRow408
      coefficientFullGramDataRow408,
    coefficientFactorTermRowData productIndexDataRow409
      coefficientFullGramDataRow409]

@[irreducible] noncomputable def coefficientFactorTermChunk041 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow410
      coefficientFullGramDataRow410,
    coefficientFactorTermRowData productIndexDataRow411
      coefficientFullGramDataRow411,
    coefficientFactorTermRowData productIndexDataRow412
      coefficientFullGramDataRow412,
    coefficientFactorTermRowData productIndexDataRow413
      coefficientFullGramDataRow413,
    coefficientFactorTermRowData productIndexDataRow414
      coefficientFullGramDataRow414,
    coefficientFactorTermRowData productIndexDataRow415
      coefficientFullGramDataRow415,
    coefficientFactorTermRowData productIndexDataRow416
      coefficientFullGramDataRow416,
    coefficientFactorTermRowData productIndexDataRow417
      coefficientFullGramDataRow417,
    coefficientFactorTermRowData productIndexDataRow418
      coefficientFullGramDataRow418,
    coefficientFactorTermRowData productIndexDataRow419
      coefficientFullGramDataRow419]

@[irreducible] noncomputable def coefficientFactorTermChunk042 :
    List (IntegerTableTerm 73033) :=
  List.flatten [
    coefficientFactorTermRowData productIndexDataRow420
      coefficientFullGramDataRow420,
    coefficientFactorTermRowData productIndexDataRow421
      coefficientFullGramDataRow421,
    coefficientFactorTermRowData productIndexDataRow422
      coefficientFullGramDataRow422,
    coefficientFactorTermRowData productIndexDataRow423
      coefficientFullGramDataRow423,
    coefficientFactorTermRowData productIndexDataRow424
      coefficientFullGramDataRow424]

@[irreducible] noncomputable def coefficientFactorTermChunks :
    List (List (IntegerTableTerm 73033)) :=
  [coefficientFactorTermChunk000,
    coefficientFactorTermChunk001,
    coefficientFactorTermChunk002,
    coefficientFactorTermChunk003,
    coefficientFactorTermChunk004,
    coefficientFactorTermChunk005,
    coefficientFactorTermChunk006,
    coefficientFactorTermChunk007,
    coefficientFactorTermChunk008,
    coefficientFactorTermChunk009,
    coefficientFactorTermChunk010,
    coefficientFactorTermChunk011,
    coefficientFactorTermChunk012,
    coefficientFactorTermChunk013,
    coefficientFactorTermChunk014,
    coefficientFactorTermChunk015,
    coefficientFactorTermChunk016,
    coefficientFactorTermChunk017,
    coefficientFactorTermChunk018,
    coefficientFactorTermChunk019,
    coefficientFactorTermChunk020,
    coefficientFactorTermChunk021,
    coefficientFactorTermChunk022,
    coefficientFactorTermChunk023,
    coefficientFactorTermChunk024,
    coefficientFactorTermChunk025,
    coefficientFactorTermChunk026,
    coefficientFactorTermChunk027,
    coefficientFactorTermChunk028,
    coefficientFactorTermChunk029,
    coefficientFactorTermChunk030,
    coefficientFactorTermChunk031,
    coefficientFactorTermChunk032,
    coefficientFactorTermChunk033,
    coefficientFactorTermChunk034,
    coefficientFactorTermChunk035,
    coefficientFactorTermChunk036,
    coefficientFactorTermChunk037,
    coefficientFactorTermChunk038,
    coefficientFactorTermChunk039,
    coefficientFactorTermChunk040,
    coefficientFactorTermChunk041,
    coefficientFactorTermChunk042]

def coefficientNegativeChunkSizes : List Nat :=
  List.replicate 19 1000 ++
    [373]

noncomputable def coefficientNegativeEdgeChunks : List (List Edge) :=
  coefficientNegativeChunkSizes.splitLengths negativeEdges

noncomputable def coefficientNegativeTermChunk
    (chunk : Nat) : List (IntegerTableTerm 73033) :=
  (coefficientNegativeEdgeChunks.getD chunk []).flatMap
    negativeEdgeTermRow

def coefficientPositiveChunkSizes : List Nat :=
  List.replicate 17 1000 ++
    [143]

noncomputable def coefficientPositiveEdgeChunks : List (List Edge) :=
  coefficientPositiveChunkSizes.splitLengths positiveEdges

noncomputable def coefficientPositiveTermChunk
    (chunk : Nat) : List (IntegerTableTerm 73033) :=
  (coefficientPositiveEdgeChunks.getD chunk []).flatMap
    positiveEdgeTermRow

noncomputable def coefficientSourceChunks :
    List (List (IntegerTableTerm 73033)) :=
  coefficientFactorTermChunks ++
  (List.range 20).map coefficientNegativeTermChunk ++
  (List.range 18).map coefficientPositiveTermChunk ++
  [diagonalTerms]

noncomputable def coefficientSourceChunk
    (chunk : Nat) : List (IntegerTableTerm 73033) :=
  coefficientSourceChunks.getD chunk []

end AffineSymplecticCertificate

end ConnesRigidity
