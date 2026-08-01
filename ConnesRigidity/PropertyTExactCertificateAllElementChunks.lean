
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group000
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group001
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group002
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group003
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group004
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group005
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group006
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group007
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group008
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group009
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group010
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group011
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group012
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group013
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group014
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group015
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group016
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group017
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group018
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group019
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group020
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group021
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group022
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group023
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group024
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group025
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group026
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group027
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group028
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group029
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group030
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group031
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group032
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group033
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group034
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group035
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group036
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group037
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group038
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group039
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group040
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group041
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group042
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group043
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group044
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group045
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group046
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group047
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group048
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group049
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group050
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group051
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group052
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group053
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group054
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group055
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group056
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group057
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group058
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group059
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group060
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group061
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group062
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group063
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group064
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group065
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group066
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group067
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group068
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group069
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group070
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group071
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group072
import ConnesRigidity.PropertyTExactCertificateAllElementChunks.Group073

namespace ConnesRigidity

namespace AffineSymplecticCertificate

@[irreducible] noncomputable def allElementDataGroups :
    Nat → Nat → Array Int
  | group, withinGroup =>
      if group < 74 then
        if group < 37 then
          if group < 18 then
            if group < 9 then
              if group < 4 then
                if group < 2 then
                  if group < 1 then
                    allElementDataGroup000 withinGroup
                  else
                    allElementDataGroup001 withinGroup
                else
                  if group < 3 then
                    allElementDataGroup002 withinGroup
                  else
                    allElementDataGroup003 withinGroup
              else
                if group < 6 then
                  if group < 5 then
                    allElementDataGroup004 withinGroup
                  else
                    allElementDataGroup005 withinGroup
                else
                  if group < 7 then
                    allElementDataGroup006 withinGroup
                  else
                    if group < 8 then
                      allElementDataGroup007 withinGroup
                    else
                      allElementDataGroup008 withinGroup
            else
              if group < 13 then
                if group < 11 then
                  if group < 10 then
                    allElementDataGroup009 withinGroup
                  else
                    allElementDataGroup010 withinGroup
                else
                  if group < 12 then
                    allElementDataGroup011 withinGroup
                  else
                    allElementDataGroup012 withinGroup
              else
                if group < 15 then
                  if group < 14 then
                    allElementDataGroup013 withinGroup
                  else
                    allElementDataGroup014 withinGroup
                else
                  if group < 16 then
                    allElementDataGroup015 withinGroup
                  else
                    if group < 17 then
                      allElementDataGroup016 withinGroup
                    else
                      allElementDataGroup017 withinGroup
          else
            if group < 27 then
              if group < 22 then
                if group < 20 then
                  if group < 19 then
                    allElementDataGroup018 withinGroup
                  else
                    allElementDataGroup019 withinGroup
                else
                  if group < 21 then
                    allElementDataGroup020 withinGroup
                  else
                    allElementDataGroup021 withinGroup
              else
                if group < 24 then
                  if group < 23 then
                    allElementDataGroup022 withinGroup
                  else
                    allElementDataGroup023 withinGroup
                else
                  if group < 25 then
                    allElementDataGroup024 withinGroup
                  else
                    if group < 26 then
                      allElementDataGroup025 withinGroup
                    else
                      allElementDataGroup026 withinGroup
            else
              if group < 32 then
                if group < 29 then
                  if group < 28 then
                    allElementDataGroup027 withinGroup
                  else
                    allElementDataGroup028 withinGroup
                else
                  if group < 30 then
                    allElementDataGroup029 withinGroup
                  else
                    if group < 31 then
                      allElementDataGroup030 withinGroup
                    else
                      allElementDataGroup031 withinGroup
              else
                if group < 34 then
                  if group < 33 then
                    allElementDataGroup032 withinGroup
                  else
                    allElementDataGroup033 withinGroup
                else
                  if group < 35 then
                    allElementDataGroup034 withinGroup
                  else
                    if group < 36 then
                      allElementDataGroup035 withinGroup
                    else
                      allElementDataGroup036 withinGroup
        else
          if group < 55 then
            if group < 46 then
              if group < 41 then
                if group < 39 then
                  if group < 38 then
                    allElementDataGroup037 withinGroup
                  else
                    allElementDataGroup038 withinGroup
                else
                  if group < 40 then
                    allElementDataGroup039 withinGroup
                  else
                    allElementDataGroup040 withinGroup
              else
                if group < 43 then
                  if group < 42 then
                    allElementDataGroup041 withinGroup
                  else
                    allElementDataGroup042 withinGroup
                else
                  if group < 44 then
                    allElementDataGroup043 withinGroup
                  else
                    if group < 45 then
                      allElementDataGroup044 withinGroup
                    else
                      allElementDataGroup045 withinGroup
            else
              if group < 50 then
                if group < 48 then
                  if group < 47 then
                    allElementDataGroup046 withinGroup
                  else
                    allElementDataGroup047 withinGroup
                else
                  if group < 49 then
                    allElementDataGroup048 withinGroup
                  else
                    allElementDataGroup049 withinGroup
              else
                if group < 52 then
                  if group < 51 then
                    allElementDataGroup050 withinGroup
                  else
                    allElementDataGroup051 withinGroup
                else
                  if group < 53 then
                    allElementDataGroup052 withinGroup
                  else
                    if group < 54 then
                      allElementDataGroup053 withinGroup
                    else
                      allElementDataGroup054 withinGroup
          else
            if group < 64 then
              if group < 59 then
                if group < 57 then
                  if group < 56 then
                    allElementDataGroup055 withinGroup
                  else
                    allElementDataGroup056 withinGroup
                else
                  if group < 58 then
                    allElementDataGroup057 withinGroup
                  else
                    allElementDataGroup058 withinGroup
              else
                if group < 61 then
                  if group < 60 then
                    allElementDataGroup059 withinGroup
                  else
                    allElementDataGroup060 withinGroup
                else
                  if group < 62 then
                    allElementDataGroup061 withinGroup
                  else
                    if group < 63 then
                      allElementDataGroup062 withinGroup
                    else
                      allElementDataGroup063 withinGroup
            else
              if group < 69 then
                if group < 66 then
                  if group < 65 then
                    allElementDataGroup064 withinGroup
                  else
                    allElementDataGroup065 withinGroup
                else
                  if group < 67 then
                    allElementDataGroup066 withinGroup
                  else
                    if group < 68 then
                      allElementDataGroup067 withinGroup
                    else
                      allElementDataGroup068 withinGroup
              else
                if group < 71 then
                  if group < 70 then
                    allElementDataGroup069 withinGroup
                  else
                    allElementDataGroup070 withinGroup
                else
                  if group < 72 then
                    allElementDataGroup071 withinGroup
                  else
                    if group < 73 then
                      allElementDataGroup072 withinGroup
                    else
                      allElementDataGroup073 withinGroup
      else
        #[]

@[irreducible] noncomputable def allElementDataRow (i : Nat) : Array Int :=
  allElementDataGroups (i / 1000) (i % 1000)

end AffineSymplecticCertificate

end ConnesRigidity
