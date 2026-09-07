/-
  Bridge Theorem: K=18 Chunked Bridge Verification
  Proved by: checkBridgeCantorPow2_of_chunked 18 1594323 162
  Split into 3 parts to avoid stack overflow (162 native_decide calls).
-/

import Mathlib.Tactic
import ErdosTernary.BridgeCantorChunked
import ErdosTernary.BridgeK18Part1
import ErdosTernary.BridgeK18Part2
import ErdosTernary.BridgeK18Part3

open ErdosTernary.BridgeCantorChunked

namespace ErdosTernary.BridgeCantorChunkedProofs

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem checkBridgeCantorPow2_K18 :
    checkBridgeCantorPow2 18 = true := by
  apply checkBridgeCantorPow2_of_chunked 18 1594323 162
  · exact (by norm_num : 0 < 1594323)
  · native_decide
  · intro j hj; interval_cases j
    · exact BridgeK18Part1.rc_K18_0
    · exact BridgeK18Part1.rc_K18_1
    · exact BridgeK18Part1.rc_K18_2
    · exact BridgeK18Part1.rc_K18_3
    · exact BridgeK18Part1.rc_K18_4
    · exact BridgeK18Part1.rc_K18_5
    · exact BridgeK18Part1.rc_K18_6
    · exact BridgeK18Part1.rc_K18_7
    · exact BridgeK18Part1.rc_K18_8
    · exact BridgeK18Part1.rc_K18_9
    · exact BridgeK18Part1.rc_K18_10
    · exact BridgeK18Part1.rc_K18_11
    · exact BridgeK18Part1.rc_K18_12
    · exact BridgeK18Part1.rc_K18_13
    · exact BridgeK18Part1.rc_K18_14
    · exact BridgeK18Part1.rc_K18_15
    · exact BridgeK18Part1.rc_K18_16
    · exact BridgeK18Part1.rc_K18_17
    · exact BridgeK18Part1.rc_K18_18
    · exact BridgeK18Part1.rc_K18_19
    · exact BridgeK18Part1.rc_K18_20
    · exact BridgeK18Part1.rc_K18_21
    · exact BridgeK18Part1.rc_K18_22
    · exact BridgeK18Part1.rc_K18_23
    · exact BridgeK18Part1.rc_K18_24
    · exact BridgeK18Part1.rc_K18_25
    · exact BridgeK18Part1.rc_K18_26
    · exact BridgeK18Part1.rc_K18_27
    · exact BridgeK18Part1.rc_K18_28
    · exact BridgeK18Part1.rc_K18_29
    · exact BridgeK18Part1.rc_K18_30
    · exact BridgeK18Part1.rc_K18_31
    · exact BridgeK18Part1.rc_K18_32
    · exact BridgeK18Part1.rc_K18_33
    · exact BridgeK18Part1.rc_K18_34
    · exact BridgeK18Part1.rc_K18_35
    · exact BridgeK18Part1.rc_K18_36
    · exact BridgeK18Part1.rc_K18_37
    · exact BridgeK18Part1.rc_K18_38
    · exact BridgeK18Part1.rc_K18_39
    · exact BridgeK18Part1.rc_K18_40
    · exact BridgeK18Part1.rc_K18_41
    · exact BridgeK18Part1.rc_K18_42
    · exact BridgeK18Part1.rc_K18_43
    · exact BridgeK18Part1.rc_K18_44
    · exact BridgeK18Part1.rc_K18_45
    · exact BridgeK18Part1.rc_K18_46
    · exact BridgeK18Part1.rc_K18_47
    · exact BridgeK18Part1.rc_K18_48
    · exact BridgeK18Part1.rc_K18_49
    · exact BridgeK18Part1.rc_K18_50
    · exact BridgeK18Part1.rc_K18_51
    · exact BridgeK18Part1.rc_K18_52
    · exact BridgeK18Part1.rc_K18_53
    · exact BridgeK18Part2.rc_K18_54
    · exact BridgeK18Part2.rc_K18_55
    · exact BridgeK18Part2.rc_K18_56
    · exact BridgeK18Part2.rc_K18_57
    · exact BridgeK18Part2.rc_K18_58
    · exact BridgeK18Part2.rc_K18_59
    · exact BridgeK18Part2.rc_K18_60
    · exact BridgeK18Part2.rc_K18_61
    · exact BridgeK18Part2.rc_K18_62
    · exact BridgeK18Part2.rc_K18_63
    · exact BridgeK18Part2.rc_K18_64
    · exact BridgeK18Part2.rc_K18_65
    · exact BridgeK18Part2.rc_K18_66
    · exact BridgeK18Part2.rc_K18_67
    · exact BridgeK18Part2.rc_K18_68
    · exact BridgeK18Part2.rc_K18_69
    · exact BridgeK18Part2.rc_K18_70
    · exact BridgeK18Part2.rc_K18_71
    · exact BridgeK18Part2.rc_K18_72
    · exact BridgeK18Part2.rc_K18_73
    · exact BridgeK18Part2.rc_K18_74
    · exact BridgeK18Part2.rc_K18_75
    · exact BridgeK18Part2.rc_K18_76
    · exact BridgeK18Part2.rc_K18_77
    · exact BridgeK18Part2.rc_K18_78
    · exact BridgeK18Part2.rc_K18_79
    · exact BridgeK18Part2.rc_K18_80
    · exact BridgeK18Part2.rc_K18_81
    · exact BridgeK18Part2.rc_K18_82
    · exact BridgeK18Part2.rc_K18_83
    · exact BridgeK18Part2.rc_K18_84
    · exact BridgeK18Part2.rc_K18_85
    · exact BridgeK18Part2.rc_K18_86
    · exact BridgeK18Part2.rc_K18_87
    · exact BridgeK18Part2.rc_K18_88
    · exact BridgeK18Part2.rc_K18_89
    · exact BridgeK18Part2.rc_K18_90
    · exact BridgeK18Part2.rc_K18_91
    · exact BridgeK18Part2.rc_K18_92
    · exact BridgeK18Part2.rc_K18_93
    · exact BridgeK18Part2.rc_K18_94
    · exact BridgeK18Part2.rc_K18_95
    · exact BridgeK18Part2.rc_K18_96
    · exact BridgeK18Part2.rc_K18_97
    · exact BridgeK18Part2.rc_K18_98
    · exact BridgeK18Part2.rc_K18_99
    · exact BridgeK18Part2.rc_K18_100
    · exact BridgeK18Part2.rc_K18_101
    · exact BridgeK18Part2.rc_K18_102
    · exact BridgeK18Part2.rc_K18_103
    · exact BridgeK18Part2.rc_K18_104
    · exact BridgeK18Part2.rc_K18_105
    · exact BridgeK18Part2.rc_K18_106
    · exact BridgeK18Part2.rc_K18_107
    · exact BridgeK18Part3.rc_K18_108
    · exact BridgeK18Part3.rc_K18_109
    · exact BridgeK18Part3.rc_K18_110
    · exact BridgeK18Part3.rc_K18_111
    · exact BridgeK18Part3.rc_K18_112
    · exact BridgeK18Part3.rc_K18_113
    · exact BridgeK18Part3.rc_K18_114
    · exact BridgeK18Part3.rc_K18_115
    · exact BridgeK18Part3.rc_K18_116
    · exact BridgeK18Part3.rc_K18_117
    · exact BridgeK18Part3.rc_K18_118
    · exact BridgeK18Part3.rc_K18_119
    · exact BridgeK18Part3.rc_K18_120
    · exact BridgeK18Part3.rc_K18_121
    · exact BridgeK18Part3.rc_K18_122
    · exact BridgeK18Part3.rc_K18_123
    · exact BridgeK18Part3.rc_K18_124
    · exact BridgeK18Part3.rc_K18_125
    · exact BridgeK18Part3.rc_K18_126
    · exact BridgeK18Part3.rc_K18_127
    · exact BridgeK18Part3.rc_K18_128
    · exact BridgeK18Part3.rc_K18_129
    · exact BridgeK18Part3.rc_K18_130
    · exact BridgeK18Part3.rc_K18_131
    · exact BridgeK18Part3.rc_K18_132
    · exact BridgeK18Part3.rc_K18_133
    · exact BridgeK18Part3.rc_K18_134
    · exact BridgeK18Part3.rc_K18_135
    · exact BridgeK18Part3.rc_K18_136
    · exact BridgeK18Part3.rc_K18_137
    · exact BridgeK18Part3.rc_K18_138
    · exact BridgeK18Part3.rc_K18_139
    · exact BridgeK18Part3.rc_K18_140
    · exact BridgeK18Part3.rc_K18_141
    · exact BridgeK18Part3.rc_K18_142
    · exact BridgeK18Part3.rc_K18_143
    · exact BridgeK18Part3.rc_K18_144
    · exact BridgeK18Part3.rc_K18_145
    · exact BridgeK18Part3.rc_K18_146
    · exact BridgeK18Part3.rc_K18_147
    · exact BridgeK18Part3.rc_K18_148
    · exact BridgeK18Part3.rc_K18_149
    · exact BridgeK18Part3.rc_K18_150
    · exact BridgeK18Part3.rc_K18_151
    · exact BridgeK18Part3.rc_K18_152
    · exact BridgeK18Part3.rc_K18_153
    · exact BridgeK18Part3.rc_K18_154
    · exact BridgeK18Part3.rc_K18_155
    · exact BridgeK18Part3.rc_K18_156
    · exact BridgeK18Part3.rc_K18_157
    · exact BridgeK18Part3.rc_K18_158
    · exact BridgeK18Part3.rc_K18_159
    · exact BridgeK18Part3.rc_K18_160
    · exact BridgeK18Part3.rc_K18_161

end ErdosTernary.BridgeCantorChunkedProofs
