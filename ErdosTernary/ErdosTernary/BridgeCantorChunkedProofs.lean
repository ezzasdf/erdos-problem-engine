/-
  Auto-generated range-check chunk proofs for K=15,16,17.
  Each chunk covers a range of size 3^13 = 1,594,323.
  Proved by native_decide on the range-parallel bridge check.
-/

import ErdosTernary.BridgeCantorChunked

open ErdosTernary.BridgeCantorChunked

-- K=15: uK K = 9565938, chunk_size = 1594323, num_chunks = 6

set_option maxHeartbeats 20000000 in
private theorem rc_K15_0 :
    rangeCheck 15 0 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K15_1 :
    rangeCheck 15 1594323 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K15_2 :
    rangeCheck 15 3188646 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K15_3 :
    rangeCheck 15 4782969 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K15_4 :
    rangeCheck 15 6377292 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K15_5 :
    rangeCheck 15 7971615 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
theorem checkBridgeCantorPow2_K15 :
    checkBridgeCantorPow2 15 = true := by
  apply checkBridgeCantorPow2_of_chunked 15 1594323 6
  · exact (by norm_num : 0 < 1594323)
  · native_decide
  · intro j hj; interval_cases j
    · exact rc_K15_0
    · exact rc_K15_1
    · exact rc_K15_2
    · exact rc_K15_3
    · exact rc_K15_4
    · exact rc_K15_5

-- K=16: uK K = 28697814, chunk_size = 1594323, num_chunks = 18

set_option maxHeartbeats 20000000 in
private theorem rc_K16_0 :
    rangeCheck 16 0 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_1 :
    rangeCheck 16 1594323 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_2 :
    rangeCheck 16 3188646 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_3 :
    rangeCheck 16 4782969 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_4 :
    rangeCheck 16 6377292 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_5 :
    rangeCheck 16 7971615 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_6 :
    rangeCheck 16 9565938 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_7 :
    rangeCheck 16 11160261 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_8 :
    rangeCheck 16 12754584 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_9 :
    rangeCheck 16 14348907 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_10 :
    rangeCheck 16 15943230 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_11 :
    rangeCheck 16 17537553 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_12 :
    rangeCheck 16 19131876 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_13 :
    rangeCheck 16 20726199 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_14 :
    rangeCheck 16 22320522 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_15 :
    rangeCheck 16 23914845 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_16 :
    rangeCheck 16 25509168 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K16_17 :
    rangeCheck 16 27103491 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
theorem checkBridgeCantorPow2_K16 :
    checkBridgeCantorPow2 16 = true := by
  apply checkBridgeCantorPow2_of_chunked 16 1594323 18
  · exact (by norm_num : 0 < 1594323)
  · native_decide
  · intro j hj; interval_cases j
    · exact rc_K16_0
    · exact rc_K16_1
    · exact rc_K16_2
    · exact rc_K16_3
    · exact rc_K16_4
    · exact rc_K16_5
    · exact rc_K16_6
    · exact rc_K16_7
    · exact rc_K16_8
    · exact rc_K16_9
    · exact rc_K16_10
    · exact rc_K16_11
    · exact rc_K16_12
    · exact rc_K16_13
    · exact rc_K16_14
    · exact rc_K16_15
    · exact rc_K16_16
    · exact rc_K16_17

-- K=17: uK K = 86093442, chunk_size = 1594323, num_chunks = 54

set_option maxHeartbeats 20000000 in
private theorem rc_K17_0 :
    rangeCheck 17 0 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_1 :
    rangeCheck 17 1594323 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_2 :
    rangeCheck 17 3188646 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_3 :
    rangeCheck 17 4782969 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_4 :
    rangeCheck 17 6377292 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_5 :
    rangeCheck 17 7971615 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_6 :
    rangeCheck 17 9565938 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_7 :
    rangeCheck 17 11160261 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_8 :
    rangeCheck 17 12754584 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_9 :
    rangeCheck 17 14348907 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_10 :
    rangeCheck 17 15943230 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_11 :
    rangeCheck 17 17537553 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_12 :
    rangeCheck 17 19131876 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_13 :
    rangeCheck 17 20726199 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_14 :
    rangeCheck 17 22320522 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_15 :
    rangeCheck 17 23914845 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_16 :
    rangeCheck 17 25509168 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_17 :
    rangeCheck 17 27103491 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_18 :
    rangeCheck 17 28697814 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_19 :
    rangeCheck 17 30292137 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_20 :
    rangeCheck 17 31886460 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_21 :
    rangeCheck 17 33480783 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_22 :
    rangeCheck 17 35075106 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_23 :
    rangeCheck 17 36669429 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_24 :
    rangeCheck 17 38263752 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_25 :
    rangeCheck 17 39858075 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_26 :
    rangeCheck 17 41452398 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_27 :
    rangeCheck 17 43046721 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_28 :
    rangeCheck 17 44641044 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_29 :
    rangeCheck 17 46235367 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_30 :
    rangeCheck 17 47829690 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_31 :
    rangeCheck 17 49424013 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_32 :
    rangeCheck 17 51018336 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_33 :
    rangeCheck 17 52612659 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_34 :
    rangeCheck 17 54206982 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_35 :
    rangeCheck 17 55801305 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_36 :
    rangeCheck 17 57395628 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_37 :
    rangeCheck 17 58989951 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_38 :
    rangeCheck 17 60584274 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_39 :
    rangeCheck 17 62178597 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_40 :
    rangeCheck 17 63772920 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_41 :
    rangeCheck 17 65367243 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_42 :
    rangeCheck 17 66961566 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_43 :
    rangeCheck 17 68555889 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_44 :
    rangeCheck 17 70150212 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_45 :
    rangeCheck 17 71744535 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_46 :
    rangeCheck 17 73338858 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_47 :
    rangeCheck 17 74933181 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_48 :
    rangeCheck 17 76527504 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_49 :
    rangeCheck 17 78121827 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_50 :
    rangeCheck 17 79716150 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_51 :
    rangeCheck 17 81310473 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_52 :
    rangeCheck 17 82904796 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
private theorem rc_K17_53 :
    rangeCheck 17 84499119 1594323 = true := by
  native_decide

set_option maxHeartbeats 20000000 in
theorem checkBridgeCantorPow2_K17 :
    checkBridgeCantorPow2 17 = true := by
  apply checkBridgeCantorPow2_of_chunked 17 1594323 54
  · exact (by norm_num : 0 < 1594323)
  · native_decide
  · intro j hj; interval_cases j
    · exact rc_K17_0
    · exact rc_K17_1
    · exact rc_K17_2
    · exact rc_K17_3
    · exact rc_K17_4
    · exact rc_K17_5
    · exact rc_K17_6
    · exact rc_K17_7
    · exact rc_K17_8
    · exact rc_K17_9
    · exact rc_K17_10
    · exact rc_K17_11
    · exact rc_K17_12
    · exact rc_K17_13
    · exact rc_K17_14
    · exact rc_K17_15
    · exact rc_K17_16
    · exact rc_K17_17
    · exact rc_K17_18
    · exact rc_K17_19
    · exact rc_K17_20
    · exact rc_K17_21
    · exact rc_K17_22
    · exact rc_K17_23
    · exact rc_K17_24
    · exact rc_K17_25
    · exact rc_K17_26
    · exact rc_K17_27
    · exact rc_K17_28
    · exact rc_K17_29
    · exact rc_K17_30
    · exact rc_K17_31
    · exact rc_K17_32
    · exact rc_K17_33
    · exact rc_K17_34
    · exact rc_K17_35
    · exact rc_K17_36
    · exact rc_K17_37
    · exact rc_K17_38
    · exact rc_K17_39
    · exact rc_K17_40
    · exact rc_K17_41
    · exact rc_K17_42
    · exact rc_K17_43
    · exact rc_K17_44
    · exact rc_K17_45
    · exact rc_K17_46
    · exact rc_K17_47
    · exact rc_K17_48
    · exact rc_K17_49
    · exact rc_K17_50
    · exact rc_K17_51
    · exact rc_K17_52
    · exact rc_K17_53

 -- Total: 78 native_decide calls
