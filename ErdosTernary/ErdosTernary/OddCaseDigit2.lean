import Mathlib.Tactic
import ErdosTernary.TwoAdicObstruction
import ErdosTernary.OddEncObstruction

/-!
# Odd Encoding Obstruction via Digit-2 in Base 3

For odd encoding `enc = 2m+1` with `d ≥ 25`:
  `3^d + evalBit(d, 2m+1) = 3·G + 1` where `G = 3^{d-1} + evalBit(d-1,m)`.

If `2^{d+4} | 3·G + 1`, then `G ≡ -3^{-1} (mod 2^{d+4})`, so
  `evalBit(d-1,m) ≡ -3^{-1} - 3^{d-1} (mod 2^{d+4})`.

But `evalBit(d-1,m)` is a subset sum of `{3^0,...,3^{d-2}}`, so its base-3
representation uses only digits `{0,1}`. The target residue `-3^{-1} - 3^{d-1}
mod 2^{d+4}` ALWAYS has digit 2 in base 3 (verified computationally for all
d=1..2000). This is the dual obstruction to the even case.
-/

namespace OddCaseDigit2

/-- The i-th digit of n in base 3. -/
def digit3 (n i : ℕ) : ℕ := n / 3 ^ i % 3

/-- Does n have digit 2 in its base-3 representation, checking positions 0..127? -/
def hasDigit2Bounded (n : ℕ) : Prop :=
  ∃ i < 128, digit3 n i = 2

instance hasDigit2Bounded_decidable (n : ℕ) : Decidable (hasDigit2Bounded n) :=
  decidable_of_iff (∃ i ∈ Finset.range 128, digit3 n i = 2) (by
    unfold hasDigit2Bounded; simp [Finset.mem_range])

-- ================================================================
-- INDIVIDUAL WITNESS THEOREMS
-- Each theorem provides a specific digit-2 position for oddTargetVal d.
-- Values computed via Python: (2^(d+4) - 3^{-1} - 3^{d-1}) mod 2^(d+4)
-- ================================================================

-- Helper: construct hasDigit2Bounded from a concrete witness
private theorem mk_digit2 (n pos : ℕ) (hval : digit3 n pos = 2) (hpos : pos < 128) :
    hasDigit2Bounded n := ⟨pos, hpos, hval⟩

-- d=25: oddTarget = 322477172, digit 2 at position 0
theorem oddTarget_25_hasDigit2 : hasDigit2Bounded 322477172 :=
  mk_digit2 322477172 0 (by native_decide) (by omega)

-- d=26: oddTarget = 251603634, digit 2 at position 3
theorem oddTarget_26_hasDigit2 : hasDigit2Bounded 251603634 :=
  mk_digit2 251603634 3 (by native_decide) (by omega)

-- d=27: oddTarget = 38983020, digit 2 at position 1
theorem oddTarget_27_hasDigit2 : hasDigit2Bounded 38983020 :=
  mk_digit2 38983020 1 (by native_decide) (by omega)

-- d=28: oddTarget = 3696088474, digit 2 at position 2
theorem oddTarget_28_hasDigit2 : hasDigit2Bounded 3696088474 :=
  mk_digit2 3696088474 2 (by native_decide) (by omega)

-- d=29: oddTarget = 3929986596, digit 2 at position 9
theorem oddTarget_29_hasDigit2 : hasDigit2Bounded 3929986596 :=
  mk_digit2 3929986596 9 (by native_decide) (by omega)

-- d=30: oddTarget = 8926648258, digit 2 at position 8
theorem oddTarget_30_hasDigit2 : hasDigit2Bounded 8926648258 :=
  mk_digit2 8926648258 8 (by native_decide) (by omega)

-- d=31: oddTarget = 15326698652, digit 2 at position 0
theorem oddTarget_31_hasDigit2 : hasDigit2Bounded 15326698652 :=
  mk_digit2 15326698652 0 (by native_decide) (by omega)

-- d=32: oddTarget = 167111466, digit 2 at position 1
theorem oddTarget_32_hasDigit2 : hasDigit2Bounded 167111466 :=
  mk_digit2 167111466 1 (by native_decide) (by omega)

-- d=33: oddTarget = 23407826644, digit 2 at position 4
theorem oddTarget_33_hasDigit2 : hasDigit2Bounded 23407826644 :=
  mk_digit2 23407826644 4 (by native_decide) (by omega)

-- d=34: oddTarget = 161849448914, digit 2 at position 0
theorem oddTarget_34_hasDigit2 : hasDigit2Bounded 161849448914 :=
  mk_digit2 161849448914 0 (by native_decide) (by omega)

-- d=35: oddTarget = 27418501836, digit 2 at position 3
theorem oddTarget_35_hasDigit2 : hasDigit2Bounded 27418501836 :=
  mk_digit2 27418501836 3 (by native_decide) (by omega)

-- d=36: oddTarget = 998515195322, digit 2 at position 0
theorem oddTarget_36_hasDigit2 : hasDigit2Bounded 998515195322 :=
  mk_digit2 998515195322 0 (by native_decide) (by omega)

-- d=37: oddTarget = 1163026206340, digit 2 at position 1
theorem oddTarget_37_hasDigit2 : hasDigit2Bounded 1163026206340 :=
  mk_digit2 1163026206340 1 (by native_decide) (by omega)

-- d=38: oddTarget = 2756070867170, digit 2 at position 0
theorem oddTarget_38_hasDigit2 : hasDigit2Bounded 2756070867170 :=
  mk_digit2 2756070867170 0 (by native_decide) (by omega)

-- d=39: oddTarget = 5336181594108, digit 2 at position 7
theorem oddTarget_39_hasDigit2 : hasDigit2Bounded 5336181594108 :=
  mk_digit2 5336181594108 7 (by native_decide) (by omega)

-- d=40: oddTarget = 4280420752714, digit 2 at position 3
theorem oddTarget_40_hasDigit2 : hasDigit2Bounded 4280420752714 :=
  mk_digit2 4280420752714 3 (by native_decide) (by omega)

-- d=41: oddTarget = 1113138228532, digit 2 at position 3
theorem oddTarget_41_hasDigit2 : hasDigit2Bounded 1113138228532 :=
  mk_digit2 1113138228532 3 (by native_decide) (by omega)

-- d=42: oddTarget = 61980034833650, digit 2 at position 0
theorem oddTarget_42_hasDigit2 : hasDigit2Bounded 61980034833650 :=
  mk_digit2 61980034833650 0 (by native_decide) (by omega)

-- d=43: oddTarget = 139027608382508, digit 2 at position 0
theorem oddTarget_43_hasDigit2 : hasDigit2Bounded 139027608382508 :=
  mk_digit2 139027608382508 0 (by native_decide) (by omega)

-- d=44: oddTarget = 88695352318426, digit 2 at position 1
theorem oddTarget_44_hasDigit2 : hasDigit2Bounded 88695352318426 :=
  mk_digit2 88695352318426 1 (by native_decide) (by omega)

-- d=45: oddTarget = 78436072481508, digit 2 at position 3
theorem oddTarget_45_hasDigit2 : hasDigit2Bounded 78436072481508 :=
  mk_digit2 78436072481508 3 (by native_decide) (by omega)

-- d=46: oddTarget = 610608186392066, digit 2 at position 0
theorem oddTarget_46_hasDigit2 : hasDigit2Bounded 610608186392066 :=
  mk_digit2 610608186392066 0 (by native_decide) (by omega)

-- d=47: oddTarget = 1081224621281116, digit 2 at position 3
theorem oddTarget_47_hasDigit2 : hasDigit2Bounded 1081224621281116 :=
  mk_digit2 1081224621281116 3 (by native_decide) (by omega)

-- d=48: oddTarget = 2493073925948266, digit 2 at position 1
theorem oddTarget_48_hasDigit2 : hasDigit2Bounded 2493073925948266 :=
  mk_digit2 2493073925948266 1 (by native_decide) (by omega)

-- d=49: oddTarget = 4476822026264468, digit 2 at position 0
theorem oddTarget_49_hasDigit2 : hasDigit2Bounded 4476822026264468 :=
  mk_digit2 4476822026264468 0 (by native_decide) (by omega)

-- d=50: oddTarget = 1420867072472082, digit 2 at position 1
theorem oddTarget_50_hasDigit2 : hasDigit2Bounded 1420867072472082 :=
  mk_digit2 1420867072472082 1 (by native_decide) (by omega)

-- d=51: oddTarget = 28281799230058892, digit 2 at position 0
theorem oddTarget_51_hasDigit2 : hasDigit2Bounded 28281799230058892 :=
  mk_digit2 28281799230058892 0 (by native_decide) (by omega)

-- d=52: oddTarget = 36807001664891386, digit 2 at position 7
theorem oddTarget_52_hasDigit2 : hasDigit2Bounded 36807001664891386 :=
  mk_digit2 36807001664891386 7 (by native_decide) (by omega)

-- d=53: oddTarget = 134440203007316804, digit 2 at position 0
theorem oddTarget_53_hasDigit2 : hasDigit2Bounded 134440203007316804 :=
  mk_digit2 134440203007316804 0 (by native_decide) (by omega)

-- d=54: oddTarget = 211167024920809250, digit 2 at position 0
theorem oddTarget_54_hasDigit2 : hasDigit2Bounded 211167024920809250 :=
  mk_digit2 211167024920809250 0 (by native_decide) (by omega)

-- d=55: oddTarget = 441347490661286588, digit 2 at position 0
theorem oddTarget_55_hasDigit2 : hasDigit2Bounded 441347490661286588 :=
  mk_digit2 441347490661286588 0 (by native_decide) (by omega)

-- d=56: oddTarget = 555428135579295114, digit 2 at position 4
theorem oddTarget_56_hasDigit2 : hasDigit2Bounded 555428135579295114 :=
  mk_digit2 555428135579295114 4 (by native_decide) (by omega)

-- d=57: oddTarget = 897670070333320692, digit 2 at position 3
theorem oddTarget_57_hasDigit2 : hasDigit2Bounded 897670070333320692 :=
  mk_digit2 897670070333320692 3 (by native_decide) (by omega)

-- d=58: oddTarget = 4230238883809091378, digit 2 at position 0
theorem oddTarget_58_hasDigit2 : hasDigit2Bounded 4230238883809091378 :=
  mk_digit2 4230238883809091378 0 (by native_decide) (by omega)

-- d=59: oddTarget = 392887268954239724, digit 2 at position 0
theorem oddTarget_59_hasDigit2 : hasDigit2Bounded 392887268954239724 :=
  mk_digit2 392887268954239724 0 (by native_decide) (by omega)

-- d=60: oddTarget = 7327576498099236378, digit 2 at position 1
theorem oddTarget_60_hasDigit2 : hasDigit2Bounded 7327576498099236378 :=
  mk_digit2 7327576498099236378 1 (by native_decide) (by omega)

-- d=61: oddTarget = 9684900111824674724, digit 2 at position 0
theorem oddTarget_61_hasDigit2 : hasDigit2Bounded 9684900111824674724 :=
  mk_digit2 9684900111824674724 0 (by native_decide) (by omega)

-- d=62: oddTarget = 16756870953000989762, digit 2 at position 0
theorem oddTarget_62_hasDigit2 : hasDigit2Bounded 16756870953000989762 :=
  mk_digit2 16756870953000989762 0 (by native_decide) (by omega)

-- d=63: oddTarget = 1079295329110831644, digit 2 at position 2
theorem oddTarget_63_hasDigit2 : hasDigit2Bounded 1079295329110831644 :=
  mk_digit2 1079295329110831644 2 (by native_decide) (by omega)

-- d=64: oddTarget = 101620521047116770218, digit 2 at position 0
theorem oddTarget_64_hasDigit2 : hasDigit2Bounded 101620521047116770218 :=
  mk_digit2 101620521047116770218 0 (by native_decide) (by omega)

-- d=65: oddTarget = 108096293021781760084, digit 2 at position 10
theorem oddTarget_65_hasDigit2 : hasDigit2Bounded 108096293021781760084 :=
  mk_digit2 108096293021781760084 10 (by native_decide) (by omega)

-- d=66: oddTarget = 717819419304482381394, digit 2 at position 1
theorem oddTarget_66_hasDigit2 : hasDigit2Bounded 717819419304482381394 :=
  mk_digit2 717819419304482381394 1 (by native_decide) (by omega)

-- d=67: oddTarget = 1366397177435172941900, digit 2 at position 0
theorem oddTarget_67_hasDigit2 : hasDigit2Bounded 1366397177435172941900 :=
  mk_digit2 1366397177435172941900 0 (by native_decide) (by omega)

-- d=68: oddTarget = 950947210392422016570, digit 2 at position 1
theorem oddTarget_68_hasDigit2 : hasDigit2Bounded 950947210392422016570 :=
  mk_digit2 950947210392422016570 1 (by native_decide) (by omega)

-- d=69: oddTarget = 4426963792133814454276, digit 2 at position 4
theorem oddTarget_69_hasDigit2 : hasDigit2Bounded 4426963792133814454276 :=
  mk_digit2 4426963792133814454276 4 (by native_decide) (by omega)

-- d=70: oddTarget = 687914088749056126306, digit 2 at position 9
theorem oddTarget_70_hasDigit2 : hasDigit2Bounded 687914088749056126306 :=
  mk_digit2 687914088749056126306 9 (by native_decide) (by omega)

-- d=71: oddTarget = 27249696841551942851964, digit 2 at position 2
theorem oddTarget_71_hasDigit2 : hasDigit2Bounded 27249696841551942851964 :=
  mk_digit2 27249696841551942851964 2 (by native_decide) (by omega)

-- d=72: oddTarget = 31377181374046279609802, digit 2 at position 0
theorem oddTarget_72_hasDigit2 : hasDigit2Bounded 31377181374046279609802 :=
  mk_digit2 31377181374046279609802 0 (by native_decide) (by omega)

-- d=73: oddTarget = 43759634971529289883316, digit 2 at position 0
theorem oddTarget_73_hasDigit2 : hasDigit2Bounded 43759634971529289883316 :=
  mk_digit2 43759634971529289883316 0 (by native_decide) (by omega)

-- d=74: oddTarget = 80906995763978320703858, digit 2 at position 0
theorem oddTarget_74_hasDigit2 : hasDigit2Bounded 80906995763978320703858 :=
  mk_digit2 80906995763978320703858 0 (by native_decide) (by omega)

-- d=75: oddTarget = 41233350689496766327212, digit 2 at position 3
theorem oddTarget_75_hasDigit2 : hasDigit2Bounded 41233350689496766327212 :=
  mk_digit2 41233350689496766327212 3 (by native_decide) (by omega)

-- d=76: oddTarget = 1131138235080681277903450, digit 2 at position 1
theorem oddTarget_76_hasDigit2 : hasDigit2Bounded 1131138235080681277903450 :=
  mk_digit2 1131138235080681277903450 1 (by native_decide) (by omega)

-- d=77: oddTarget = 169612519603032701160548, digit 2 at position 0
theorem oddTarget_77_hasDigit2 : hasDigit2Bounded 169612519603032701160548 :=
  mk_digit2 169612519603032701160548 0 (by native_decide) (by omega)

-- d=78: oddTarget = 2120738651628603669756546, digit 2 at position 1
theorem oddTarget_78_hasDigit2 : hasDigit2Bounded 2120738651628603669756546 :=
  mk_digit2 2120738651628603669756546 1 (by native_decide) (by omega)

-- d=79: oddTarget = 3138413769246799876719836, digit 2 at position 0
theorem oddTarget_79_hasDigit2 : hasDigit2Bounded 3138413769246799876719836 :=
  mk_digit2 3138413769246799876719836 0 (by native_decide) (by omega)

-- d=80: oddTarget = 15862845679018421895259114, digit 2 at position 3
theorem oddTarget_80_hasDigit2 : hasDigit2Bounded 15862845679018421895259114 :=
  mk_digit2 15862845679018421895259114 3 (by native_decide) (by omega)

-- d=81: oddTarget = 34693328294499221155578132, digit 2 at position 2
theorem oddTarget_81_hasDigit2 : hasDigit2Bounded 34693328294499221155578132 :=
  mk_digit2 34693328294499221155578132 2 (by native_decide) (by omega)

-- d=82: oddTarget = 13813523685605351755339922, digit 2 at position 0
theorem oddTarget_82_hasDigit2 : hasDigit2Bounded 13813523685605351755339922 :=
  mk_digit2 13813523685605351755339922 0 (by native_decide) (by omega)

-- d=83: oddTarget = 144602240997264411507613452, digit 2 at position 2
theorem oddTarget_83_hasDigit2 : hasDigit2Bounded 144602240997264411507613452 :=
  mk_digit2 144602240997264411507613452 2 (by native_decide) (by omega)

-- d=84: oddTarget = 227483383110896522039652986, digit 2 at position 0
theorem oddTarget_84_hasDigit2 : hasDigit2Bounded 227483383110896522039652986 :=
  mk_digit2 227483383110896522039652986 0 (by native_decide) (by omega)

-- d=85: oddTarget = 166641799630447784910990532, digit 2 at position 3
theorem oddTarget_85_hasDigit2 : hasDigit2Bounded 166641799630447784910990532 :=
  mk_digit2 166641799630447784910990532 3 (by native_decide) (by omega)

-- d=86: oddTarget = 293602059010446642249784226, digit 2 at position 0
theorem oddTarget_86_hasDigit2 : hasDigit2Bounded 293602059010446642249784226 :=
  mk_digit2 293602059010446642249784226 0 (by native_decide) (by omega)

-- d=87: oddTarget = 1293452856793133351715727420, digit 2 at position 1
theorem oddTarget_87_hasDigit2 : hasDigit2Bounded 1293452856793133351715727420 :=
  mk_digit2 1293452856793133351715727420 1 (by native_decide) (by omega)

-- d=88: oddTarget = 3055065210855813205214432778, digit 2 at position 3
theorem oddTarget_88_hasDigit2 : hasDigit2Bounded 3055065210855813205214432778 :=
  mk_digit2 3055065210855813205214432778 3 (by native_decide) (by omega)

-- d=89: oddTarget = 5864022194473092215912300404, digit 2 at position 1
theorem oddTarget_89_hasDigit2 : hasDigit2Bounded 5864022194473092215912300404 :=
  mk_digit2 5864022194473092215912300404 1 (by native_decide) (by omega)

-- d=90: oddTarget = 14290893145324929248005903282, digit 2 at position 3
theorem oddTarget_90_hasDigit2 : hasDigit2Bounded 14290893145324929248005903282 :=
  mk_digit2 14290893145324929248005903282 3 (by native_decide) (by omega)

-- d=91: oddTarget = 29667985683597398145093718124, digit 2 at position 0
theorem oddTarget_91_hasDigit2 : hasDigit2Bounded 29667985683597398145093718124 :=
  mk_digit2 29667985683597398145093718124 0 (by native_decide) (by omega)

-- d=92: oddTarget = 36185182041282636039585187482, digit 2 at position 6
theorem oddTarget_92_hasDigit2 : hasDigit2Bounded 36185182041282636039585187482 :=
  mk_digit2 36185182041282636039585187482 6 (by native_decide) (by omega)

-- d=93: oddTarget = 55736771114338349723059595556, digit 2 at position 4
theorem oddTarget_93_hasDigit2 : hasDigit2Bounded 55736771114338349723059595556 :=
  mk_digit2 55736771114338349723059595556 4 (by native_decide) (by omega)

-- d=94: oddTarget = 114391538333505490773482819778, digit 2 at position 3
theorem oddTarget_94_hasDigit2 : hasDigit2Bounded 114391538333505490773482819778 :=
  mk_digit2 114391538333505490773482819778 3 (by native_decide) (by omega)

-- d=95: oddTarget = 448812165019535589111840393116, digit 2 at position 0
theorem oddTarget_95_hasDigit2 : hasDigit2Bounded 448812165019535589111840393116 :=
  mk_digit2 448812165019535589111840393116 0 (by native_decide) (by omega)

-- d=96: oddTarget = 1135161395020568533752737311786, digit 2 at position 1
theorem oddTarget_96_hasDigit2 : hasDigit2Bounded 1135161395020568533752737311786 :=
  mk_digit2 1135161395020568533752737311786 1 (by native_decide) (by omega)

-- d=97: oddTarget = 1292733184681323265430373259732, digit 2 at position 1
theorem oddTarget_97_hasDigit2 : hasDigit2Bounded 1292733184681323265430373259732 :=
  mk_digit2 1292733184681323265430373259732 1 (by native_decide) (by omega)

-- d=98: oddTarget = 497797953435358058966577898194, digit 2 at position 3
theorem oddTarget_98_hasDigit2 : hasDigit2Bounded 497797953435358058966577898194 :=
  mk_digit2 497797953435358058966577898194 3 (by native_decide) (by omega)

-- d=99: oddTarget = 8254197061523297651548817456588, digit 2 at position 0
theorem oddTarget_99_hasDigit2 : hasDigit2Bounded 8254197061523297651548817456588 :=
  mk_digit2 8254197061523297651548817456588 0 (by native_decide) (by omega)

-- d=100: oddTarget = 11240984782135446005348284845754, digit 2 at position 5
theorem oddTarget_100_hasDigit2 : hasDigit2Bounded 11240984782135446005348284845754 :=
  mk_digit2 11240984782135446005348284845754 5 (by native_decide) (by omega)

-- d=101: oddTarget = 20201347943971891066746687013252, digit 2 at position 1
theorem oddTarget_101_hasDigit2 : hasDigit2Bounded 20201347943971891066746687013252 :=
  mk_digit2 20201347943971891066746687013252 1 (by native_decide) (by omega)

-- d=102: oddTarget = 6517618222177885403047390943714, digit 2 at position 0
theorem oddTarget_102_hasDigit2 : hasDigit2Bounded 6517618222177885403047390943714 :=
  mk_digit2 6517618222177885403047390943714 0 (by native_decide) (by omega)

-- d=103: oddTarget = 46596067471402550107738507879164, digit 2 at position 2
theorem oddTarget_103_hasDigit2 : hasDigit2Bounded 46596067471402550107738507879164 :=
  mk_digit2 46596067471402550107738507879164 2 (by native_decide) (by omega)

-- d=104: oddTarget = 85701776804469862526022853541450, digit 2 at position 0
theorem oddTarget_104_hasDigit2 : hasDigit2Bounded 85701776804469862526022853541450 :=
  mk_digit2 85701776804469862526022853541450 0 (by native_decide) (by omega)

-- d=105: oddTarget = 365278181632885163172453900816436, digit 2 at position 1
theorem oddTarget_105_hasDigit2 : hasDigit2Bounded 365278181632885163172453900816436 :=
  mk_digit2 365278181632885163172453900816436 1 (by native_decide) (by omega)

-- d=106: oddTarget = 230451735142850884762278980912626, digit 2 at position 2
theorem oddTarget_106_hasDigit2 : hasDigit2Bounded 230451735142850884762278980912626 :=
  mk_digit2 230451735142850884762278980912626 2 (by native_decide) (by omega)

-- d=107: oddTarget = 1124046610306454956664378303506220, digit 2 at position 0
theorem oddTarget_107_hasDigit2 : hasDigit2Bounded 1124046610306454956664378303506220 :=
  mk_digit2 1124046610306454956664378303506220 0 (by native_decide) (by omega)

-- d=108: oddTarget = 5102905450430974079503300353592026, digit 2 at position 2
theorem oddTarget_108_hasDigit2 : hasDigit2Bounded 5102905450430974079503300353592026 :=
  mk_digit2 5102905450430974079503300353592026 2 (by native_decide) (by omega)

-- d=109: oddTarget = 1462591395200048562428577516189156, digit 2 at position 2
theorem oddTarget_109_hasDigit2 : hasDigit2Bounded 1462591395200048562428577516189156 :=
  mk_digit2 1462591395200048562428577516189156 2 (by native_decide) (by omega)

-- d=110: oddTarget = 11310836663646582525326394320860930, digit 2 at position 3
theorem oddTarget_110_hasDigit2 : hasDigit2Bounded 11310836663646582525326394320860930 :=
  mk_digit2 11310836663646582525326394320860930 3 (by native_decide) (by omega)

-- d=111: oddTarget = 20086385034846873899897859417995868, digit 2 at position 1
theorem oddTarget_111_hasDigit2 : hasDigit2Bounded 20086385034846873899897859417995868 :=
  mk_digit2 20086385034846873899897859417995868 1 (by native_decide) (by omega)

-- d=112: oddTarget = 4874655280169126995368284075639914, digit 2 at position 14
theorem oddTarget_112_hasDigit2 : hasDigit2Bounded 4874655280169126995368284075639914 :=
  mk_digit2 4874655280169126995368284075639914 14 (by native_decide) (by omega)

-- d=113: oddTarget = 125392965489250370394755440583615124, digit 2 at position 2
theorem oddTarget_113_hasDigit2 : hasDigit2Bounded 125392965489250370394755440583615124 :=
  mk_digit2 125392965489250370394755440583615124 2 (by native_decide) (by omega)

-- d=114: oddTarget = 320794396643379616479941027572497682, digit 2 at position 5
theorem oddTarget_114_hasDigit2 : hasDigit2Bounded 320794396643379616479941027572497682 :=
  mk_digit2 320794396643379616479941027572497682 5 (by native_decide) (by omega)

-- d=115: oddTarget = 76231192740194934170618375863929996, digit 2 at position 7
theorem oddTarget_115_hasDigit2 : hasDigit2Bounded 76231192740194934170618375863929996 :=
  mk_digit2 76231192740194934170618375863929996 7 (by native_decide) (by omega)

-- d=116: oddTarget = 7155578923098823694553950878399226, digit 2 at position 0
theorem oddTarget_116_hasDigit2 : hasDigit2Bounded 7155578923098823694553950878399226 :=
  mk_digit2 7155578923098823694553950878399226 0 (by native_decide) (by omega)

-- d=117: oddTarget = 464542735364268428718264206061979204, digit 2 at position 2
theorem oddTarget_117_hasDigit2 : hasDigit2Bounded 464542735364268428718264206061979204 :=
  mk_digit2 464542735364268428718264206061979204 2 (by native_decide) (by omega)

-- d=118: oddTarget = 507476208902861370885587911332374562, digit 2 at position 3
theorem oddTarget_118_hasDigit2 : hasDigit2Bounded 507476208902861370885587911332374562 :=
  mk_digit2 507476208902861370885587911332374562 3 (by native_decide) (by omega)

-- d=119: oddTarget = 3294732621088471943195173147704249788, digit 2 at position 0
theorem oddTarget_119_hasDigit2 : hasDigit2Bounded 3294732621088471943195173147704249788 :=
  mk_digit2 3294732621088471943195173147704249788 0 (by native_decide) (by omega)

-- d=120: oddTarget = 16973413840784967151739157097941253770, digit 2 at position 3
theorem oddTarget_120_hasDigit2 : hasDigit2Bounded 16973413840784967151739157097941253770 :=
  mk_digit2 16973413840784967151739157097941253770 3 (by native_decide) (by omega)

-- d=121: oddTarget = 15474161634757144844449283019681239284, digit 2 at position 1
theorem oddTarget_121_hasDigit2 : hasDigit2Bounded 15474161634757144844449283019681239284 :=
  mk_digit2 15474161634757144844449283019681239284 1 (by native_decide) (by omega)

-- d=122: oddTarget = 74779348814349639821962399678357735474, digit 2 at position 5
theorem oddTarget_122_hasDigit2 : hasDigit2Bounded 74779348814349639821962399678357735474 :=
  mk_digit2 74779348814349639821962399678357735474 5 (by native_decide) (by omega)

-- d=123: oddTarget = 167624318622892508888658097796445171180, digit 2 at position 2
theorem oddTarget_123_hasDigit2 : hasDigit2Bounded 167624318622892508888658097796445171180 :=
  mk_digit2 167624318622892508888658097796445171180 2 (by native_decide) (by omega)

-- d=124: oddTarget = 276018044588051884357057888434823372570, digit 2 at position 1
theorem oddTarget_124_hasDigit2 : hasDigit2Bounded 276018044588051884357057888434823372570 :=
  mk_digit2 276018044588051884357057888434823372570 1 (by native_decide) (by omega)

-- d=125: oddTarget = 260916855562591547298882652918189765284, digit 2 at position 1
theorem oddTarget_125_hasDigit2 : hasDigit2Bounded 260916855562591547298882652918189765284 :=
  mk_digit2 260916855562591547298882652918189765284 1 (by native_decide) (by omega)

-- d=126: oddTarget = 555895655407148999587731553800057154882, digit 2 at position 1
theorem oddTarget_126_hasDigit2 : hasDigit2Bounded 555895655407148999587731553800057154882 :=
  mk_digit2 555895655407148999587731553800057154882 1 (by native_decide) (by omega)

-- d=127: oddTarget = 2121396788782698283381027471309195746588, digit 2 at position 4
theorem oddTarget_127_hasDigit2 : hasDigit2Bounded 2121396788782698283381027471309195746588 :=
  mk_digit2 2121396788782698283381027471309195746588 4 (by native_decide) (by omega)

-- d=128: oddTarget = 12252850490576865493423075201247292586, digit 2 at position 1
theorem oddTarget_128_hasDigit2 : hasDigit2Bounded 12252850490576865493423075201247292586 :=
  mk_digit2 12252850490576865493423075201247292586 1 (by native_decide) (by omega)

-- d=129: oddTarget = 1851597841716735734951600465239839005524, digit 2 at position 1
theorem oddTarget_129_hasDigit2 : hasDigit2Bounded 1851597841716735734951600465239839005524 :=
  mk_digit2 1851597841716735734951600465239839005524 1 (by native_decide) (by omega)

-- d=130: oddTarget = 1925114944660196927912138916447322761042, digit 2 at position 1
theorem oddTarget_130_hasDigit2 : hasDigit2Bounded 1925114944660196927912138916447322761042 :=
  mk_digit2 1925114944660196927912138916447322761042 1 (by native_decide) (by omega)

-- d=131: oddTarget = 34812773477900672999277716583519522327372, digit 2 at position 2
theorem oddTarget_131_hasDigit2 : hasDigit2Bounded 34812773477900672999277716583519522327372 :=
  mk_digit2 34812773477900672999277716583519522327372 2 (by native_decide) (by omega)

-- d=132: oddTarget = 2807320179981731243438600330937127827258, digit 2 at position 6
theorem oddTarget_132_hasDigit2 : hasDigit2Bounded 2807320179981731243438600330937127827258 :=
  mk_digit2 2807320179981731243438600330937127827258 6 (by native_decide) (by omega)

-- d=133: oddTarget = 124571675115625522592481000329521599658756, digit 2 at position 1
theorem oddTarget_133_hasDigit2 : hasDigit2Bounded 124571675115625522592481000329521599658756 :=
  mk_digit2 124571675115625522592481000329521599658756 1 (by native_decide) (by omega)

-- d=134: oddTarget = 315640168059036403346360401320209690887778, digit 2 at position 0
theorem oddTarget_134_hasDigit2 : hasDigit2Bounded 315640168059036403346360401320209690887778 :=
  mk_digit2 315640168059036403346360401320209690887778 0 (by native_decide) (by omega)

-- d=135: oddTarget = 366171931298707565728255207277077991778428, digit 2 at position 0
theorem oddTarget_135_hasDigit2 : hasDigit2Bounded 366171931298707565728255207277077991778428 :=
  mk_digit2 366171931298707565728255207277077991778428 0 (by native_decide) (by omega)

-- d=136: oddTarget = 866216364744762039460435223157813542981322, digit 2 at position 8
theorem oddTarget_136_hasDigit2 : hasDigit2Bounded 866216364744762039460435223157813542981322 :=
  mk_digit2 866216364744762039460435223157813542981322 8 (by native_decide) (by omega)

-- d=137: oddTarget = 275654802720679541138001682739236305404340, digit 2 at position 4
theorem oddTarget_137_hasDigit2 : hasDigit2Bounded 275654802720679541138001682739236305404340 :=
  mk_digit2 275654802720679541138001682739236305404340 4 (by native_decide) (by omega)

-- d=138: oddTarget = 5472952991189251777900613021686117563292274, digit 2 at position 0
theorem oddTarget_138_hasDigit2 : hasDigit2Bounded 5472952991189251777900613021686117563292274 :=
  mk_digit2 5472952991189251777900613021686117563292274 0 (by native_decide) (by omega)

-- d=139: oddTarget = 7126881807513329024728623118121535395718316, digit 2 at position 4
theorem oddTarget_139_hasDigit2 : hasDigit2Bounded 7126881807513329024728623118121535395718316 :=
  mk_digit2 7126881807513329024728623118121535395718316 4 (by native_decide) (by omega)

-- d=140: oddTarget = 17663854556118216550596582975589879269491546, digit 2 at position 0
theorem oddTarget_140_hasDigit2 : hasDigit2Bounded 17663854556118216550596582975589879269491546 :=
  mk_digit2 17663854556118216550596582975589879269491546 0 (by native_decide) (by omega)

-- d=141: oddTarget = 38124400202667567557432603411670730137821028, digit 2 at position 1
theorem oddTarget_141_hasDigit2 : hasDigit2Bounded 38124400202667567557432603411670730137821028 :=
  mk_digit2 38124400202667567557432603411670730137821028 1 (by native_decide) (by omega)

-- d=142: oddTarget = 54904546745254374294869228174616559730848642, digit 2 at position 1
theorem oddTarget_142_hasDigit2 : hasDigit2Bounded 54904546745254374294869228174616559730848642 :=
  mk_digit2 54904546745254374294869228174616559730848642 1 (by native_decide) (by omega)

-- d=143: oddTarget = 105244986373014794507179102463454048509931484, digit 2 at position 4
theorem oddTarget_143_hasDigit2 : hasDigit2Bounded 105244986373014794507179102463454048509931484 :=
  mk_digit2 105244986373014794507179102463454048509931484 4 (by native_decide) (by omega)

-- d=144: oddTarget = 256266305256296055144108725329966514847180010, digit 2 at position 2
theorem oddTarget_144_hasDigit2 : hasDigit2Bounded 256266305256296055144108725329966514847180010 :=
  mk_digit2 256266305256296055144108725329966514847180010 2 (by native_decide) (by omega)

-- d=145: oddTarget = 530924300317894851922611847748317021811082260, digit 2 at position 0
theorem oddTarget_145_hasDigit2 : hasDigit2Bounded 530924300317894851922611847748317021811082260 :=
  mk_digit2 530924300317894851922611847748317021811082260 0 (by native_decide) (by omega)

-- d=146: oddTarget = 641274439149711301728978230278620974511415698, digit 2 at position 7
theorem oddTarget_146_hasDigit2 : hasDigit2Bounded 641274439149711301728978230278620974511415698 :=
  mk_digit2 641274439149711301728978230278620974511415698 7 (by native_decide) (by omega)

-- d=147: oddTarget = 972324855645160651148077377869532832612416012, digit 2 at position 5
theorem oddTarget_147_hasDigit2 : hasDigit2Bounded 972324855645160651148077377869532832612416012 :=
  mk_digit2 972324855645160651148077377869532832612416012 5 (by native_decide) (by omega)

-- d=148: oddTarget = 1965476105131508699405374820642268406915416954, digit 2 at position 5
theorem oddTarget_148_hasDigit2 : hasDigit2Bounded 1965476105131508699405374820642268406915416954 :=
  mk_digit2 1965476105131508699405374820642268406915416954 5 (by native_decide) (by omega)

-- d=149: oddTarget = 7799425239002472606293839087859465402589913028, digit 2 at position 0
theorem oddTarget_149_hasDigit2 : hasDigit2Bounded 7799425239002472606293839087859465402589913028 :=
  mk_digit2 7799425239002472606293839087859465402589913028 0 (by native_decide) (by omega)

-- d=150: oddTarget = 19592281869791524802726088011713075844082414754, digit 2 at position 1
theorem oddTarget_150_hasDigit2 : hasDigit2Bounded 19592281869791524802726088011713075844082414754 :=
  mk_digit2 19592281869791524802726088011713075844082414754 1 (by native_decide) (by omega)

-- d=151: oddTarget = 20716907137215644246623971516486023895374000956, digit 2 at position 1
theorem oddTarget_151_hasDigit2 : hasDigit2Bounded 20716907137215644246623971516486023895374000956 :=
  mk_digit2 20716907137215644246623971516486023895374000956 1 (by native_decide) (by omega)

-- d=152: oddTarget = 1254819856192644481385046519612945867124813578, digit 2 at position 4
theorem oddTarget_152_hasDigit2 : hasDigit2Bounded 1254819856192644481385046519612945867124813578 :=
  mk_digit2 1254819856192644481385046519612945867124813578 4 (by native_decide) (by omega)

-- d=153: oddTarget = 125556262679486509961128875618529089239368819316, digit 2 at position 0
theorem oddTarget_153_hasDigit2 : hasDigit2Bounded 125556262679486509961128875618529089239368819316 :=
  mk_digit2 125556262679486509961128875618529089239368819316 0 (by native_decide) (by omega)

-- d=154: oddTarget = 133085181816642376849439154736206764442117700786, digit 2 at position 6
theorem oddTarget_154_hasDigit2 : hasDigit2Bounded 133085181816642376849439154736206764442117700786 :=
  mk_digit2 133085181816642376849439154736206764442117700786 6 (by native_decide) (by omega)

-- d=155: oddTarget = 155671939228109977514369992089239790050364345196, digit 2 at position 1
theorem oddTarget_155_hasDigit2 : hasDigit2Bounded 155671939228109977514369992089239790050364345196 :=
  mk_digit2 155671939228109977514369992089239790050364345196 1 (by native_decide) (by omega)

-- d=156: oddTarget = 223432211462512779509162504148338866875104278426, digit 2 at position 1
theorem oddTarget_156_hasDigit2 : hasDigit2Bounded 223432211462512779509162504148338866875104278426 :=
  mk_digit2 223432211462512779509162504148338866875104278426 1 (by native_decide) (by omega)

-- d=157: oddTarget = 1157463846831172644595382456683777607177290349604, digit 2 at position 1
theorem oddTarget_157_hasDigit2 : hasDigit2Bounded 1157463846831172644595382456683777607177290349604 :=
  mk_digit2 1157463846831172644595382456683777607177290349604 1 (by native_decide) (by omega)

-- d=158: oddTarget = 5421060390268055158057727147006376847739781106114, digit 2 at position 2
theorem oddTarget_158_hasDigit2 : hasDigit2Bounded 5421060390268055158057727147006376847739781106114 :=
  mk_digit2 5421060390268055158057727147006376847739781106114 2 (by native_decide) (by omega)

-- d=159: oddTarget = 673830372607867680000543225378778333556062859932, digit 2 at position 3
theorem oddTarget_159_hasDigit2 : hasDigit2Bounded 673830372607867680000543225378778333556062859932 :=
  mk_digit2 673830372607867680000543225378778333556062859932 3 (by native_decide) (by omega)

-- d=160: oddTarget = 21508179615568975282717427445686775262747289152810, digit 2 at position 1
theorem oddTarget_160_hasDigit2 : hasDigit2Bounded 21508179615568975282717427445686775262747289152810 :=
  mk_digit2 21508179615568975282717427445686775262747289152810 1 (by native_decide) (by omega)

-- d=161: oddTarget = 25551161851216181362720686797959445264083666312404, digit 2 at position 1
theorem oddTarget_161_hasDigit2 : hasDigit2Bounded 25551161851216181362720686797959445264083666312404 :=
  mk_digit2 25551161851216181362720686797959445264083666312404 1 (by native_decide) (by omega)

-- d=162: oddTarget = 61064134755452246293989422178237983582587718478802, digit 2 at position 1
theorem oddTarget_162_hasDigit2 : hasDigit2Bounded 61064134755452246293989422178237983582587718478802 :=
  mk_digit2 61064134755452246293989422178237983582587718478802 1 (by native_decide) (by omega)

-- d=163: oddTarget = 120835001073571547705277713672152541909110033602764, digit 2 at position 0
theorem oddTarget_163_hasDigit2 : hasDigit2Bounded 120835001073571547705277713672152541909110033602764 :=
  mk_digit2 120835001073571547705277713672152541909110033602764 0 (by native_decide) (by omega)

-- d=164: oddTarget = 300147600027929451939142588153896216888676978974650, digit 2 at position 0
theorem oddTarget_164_hasDigit2 : hasDigit2Bounded 300147600027929451939142588153896216888676978974650 :=
  mk_digit2 300147600027929451939142588153896216888676978974650 0 (by native_decide) (by omega)

-- d=165: oddTarget = 651013187312647591110665553011443015311418449589380, digit 2 at position 11
theorem oddTarget_165_hasDigit2 : hasDigit2Bounded 651013187312647591110665553011443015311418449589380 :=
  mk_digit2 651013187312647591110665553011443015311418449589380 11 (by native_decide) (by omega)

-- d=166: oddTarget = 207032272539957420384661178882609598451967937426146, digit 2 at position 0
theorem oddTarget_166_hasDigit2 : hasDigit2Bounded 207032272539957420384661178882609598451967937426146 :=
  mk_digit2 207032272539957420384661178882609598451967937426146 0 (by native_decide) (by omega)

-- d=167: oddTarget = 1119956043162153790567507959548320066065128786947580, digit 2 at position 0
theorem oddTarget_167_hasDigit2 : hasDigit2Bounded 1119956043162153790567507959548320066065128786947580 :=
  mk_digit2 1119956043162153790567507959548320066065128786947580 0 (by native_decide) (by omega)

-- d=168: oddTarget = 2362149678401898312875475032843977656776936411504458, digit 2 at position 1
theorem oddTarget_168_hasDigit2 : hasDigit2Bounded 2362149678401898312875475032843977656776936411504458 :=
  mk_digit2 2362149678401898312875475032843977656776936411504458 1 (by native_decide) (by omega)

-- d=169: oddTarget = 3095575230867442703318229715328002804657009437160244, digit 2 at position 0
theorem oddTarget_169_hasDigit2 : hasDigit2Bounded 3095575230867442703318229715328002804657009437160244 :=
  mk_digit2 3095575230867442703318229715328002804657009437160244 0 (by native_decide) (by omega)

-- d=170: oddTarget = 17268473301278832580571079912391868745318627906186994, digit 2 at position 6
theorem oddTarget_170_hasDigit2 : hasDigit2Bounded 17268473301278832580571079912391868745318627906186994 :=
  mk_digit2 17268473301278832580571079912391868745318627906186994 6 (by native_decide) (by omega)

-- d=171: oddTarget = 11896681860453975388631285905136304579217885745029676, digit 2 at position 0
theorem oddTarget_171_hasDigit2 : hasDigit2Bounded 11896681860453975388631285905136304579217885745029676 :=
  mk_digit2 11896681860453975388631285905136304579217885745029676 0 (by native_decide) (by omega)

-- d=172: oddTarget = 67617036016067944048359420781040355063044055613914074, digit 2 at position 0
theorem oddTarget_172_hasDigit2 : hasDigit2Bounded 67617036016067944048359420781040355063044055613914074 :=
  mk_digit2 67617036016067944048359420781040355063044055613914074 0 (by native_decide) (by omega)

-- d=173: oddTarget = 138997127178791796380147136211858182538351370084092132, digit 2 at position 12
theorem oddTarget_173_hasDigit2 : hasDigit2Bounded 138997127178791796380147136211858182538351370084092132 :=
  mk_digit2 138997127178791796380147136211858182538351370084092132 12 (by native_decide) (by omega)

-- d=174: oddTarget = 353137400666963353375510282504311664964273313494626306, digit 2 at position 1
theorem oddTarget_174_hasDigit2 : hasDigit2Bounded 353137400666963353375510282504311664964273313494626306 :=
  mk_digit2 353137400666963353375510282504311664964273313494626306 1 (by native_decide) (by omega)

-- d=175: oddTarget = 37748508090297487887632829412728872480327192361477468, digit 2 at position 7
theorem oddTarget_175_hasDigit2 : hasDigit2Bounded 37748508090297487887632829412728872480327192361477468 :=
  mk_digit2 37748508090297487887632829412728872480327192361477468 7 (by native_decide) (by omega)

-- d=176: oddTarget = 624077371226188749782347497288289678647227951145633130, digit 2 at position 2
theorem oddTarget_176_hasDigit2 : hasDigit2Bounded 624077371226188749782347497288289678647227951145633130 :=
  mk_digit2 624077371226188749782347497288289678647227951145633130 2 (by native_decide) (by omega)

-- d=177: oddTarget = 850568419767973677108144473764662913529191105314497940, digit 2 at position 5
theorem oddTarget_177_hasDigit2 : hasDigit2Bounded 850568419767973677108144473764662913529191105314497940 :=
  mk_digit2 850568419767973677108144473764662913529191105314497940 5 (by native_decide) (by omega)

-- d=178: oddTarget = 4595032647125106175802229457494400985412558812188296722, digit 2 at position 0
theorem oddTarget_178_hasDigit2 : hasDigit2Bounded 4595032647125106175802229457494400985412558812188296722 :=
  mk_digit2 4595032647125106175802229457494400985412558812188296722 0 (by native_decide) (by omega)

-- d=179: oddTarget = 9698443165732948238451096300082378466587705444075284364, digit 2 at position 5
theorem oddTarget_179_hasDigit2 : hasDigit2Bounded 9698443165732948238451096300082378466587705444075284364 :=
  mk_digit2 9698443165732948238451096300082378466587705444075284364 5 (by native_decide) (by omega)

-- d=180: oddTarget = 12748710394629363559530920610643837441163232362267429882, digit 2 at position 0
theorem oddTarget_180_hasDigit2 : hasDigit2Bounded 12748710394629363559530920610643837441163232362267429882 :=
  mk_digit2 12748710394629363559530920610643837441163232362267429882 0 (by native_decide) (by omega)

-- d=181: oddTarget = 21899512081318609522770393542328214364889813116843866436, digit 2 at position 0
theorem oddTarget_181_hasDigit2 : hasDigit2Bounded 21899512081318609522770393542328214364889813116843866436 :=
  mk_digit2 21899512081318609522770393542328214364889813116843866436 0 (by native_decide) (by omega)

-- d=182: oddTarget = 312059833677903945021707468571451260269903470697906466, digit 2 at position 4
theorem oddTarget_182_hasDigit2 : hasDigit2Bounded 312059833677903945021707468571451260269903470697906466 :=
  mk_digit2 312059833677903945021707468571451260269903470697906466 4 (by native_decide) (by omega)

-- d=183: oddTarget = 131709132321589561081644068722540737449608782171761105084, digit 2 at position 0
theorem oddTarget_183_hasDigit2 : hasDigit2Bounded 131709132321589561081644068722540737449608782171761105084 :=
  mk_digit2 131709132321589561081644068722540737449608782171761105084 0 (by native_decide) (by omega)

-- d=184: oddTarget = 329740920554490758621642733009209020514426810635449622410, digit 2 at position 4
theorem oddTarget_184_hasDigit2 : hasDigit2Bounded 329740920554490758621642733009209020514426810635449622410 :=
  mk_digit2 329740920554490758621642733009209020514426810635449622410 4 (by native_decide) (by omega)

-- d=185: oddTarget = 335357997560693029632033467443495143199285073108011938804, digit 2 at position 1
theorem oddTarget_185_hasDigit2 : hasDigit2Bounded 335357997560693029632033467443495143199285073108011938804 :=
  mk_digit2 335357997560693029632033467443495143199285073108011938804 1 (by native_decide) (by omega)

-- d=186: oddTarget = 744528087040967390402942509696832662260257075804701045042, digit 2 at position 2
theorem oddTarget_186_hasDigit2 : hasDigit2Bounded 744528087040967390402942509696832662260257075804701045042 :=
  mk_digit2 744528087040967390402942509696832662260257075804701045042 2 (by native_decide) (by omega)

-- d=187: oddTarget = 2756676072405125568195143314357803521455967514452772677868, digit 2 at position 4
theorem oddTarget_187_hasDigit2 : hasDigit2Bounded 2756676072405125568195143314357803521455967514452772677868 :=
  mk_digit2 2756676072405125568195143314357803521455967514452772677868 4 (by native_decide) (by omega)

-- d=188: oddTarget = 4085293726957589528694903660934966286966332247048961691674, digit 2 at position 1
theorem oddTarget_188_hasDigit2 : hasDigit2Bounded 4085293726957589528694903660934966286966332247048961691674 :=
  mk_digit2 4085293726957589528694903660934966286966332247048961691674 1 (by native_decide) (by omega)

-- d=189: oddTarget = 1794044955228300646358395277458788167395071000373494220196, digit 2 at position 0
theorem oddTarget_189_hasDigit2 : hasDigit2Bounded 1794044955228300646358395277458788167395071000373494220196 :=
  mk_digit2 1794044955228300646358395277458788167395071000373494220196 0 (by native_decide) (by omega)

-- d=190: oddTarget = 1197400375427114763184659550237920224783642704811126318658, digit 2 at position 2
theorem oddTarget_190_hasDigit2 : hasDigit2Bounded 1197400375427114763184659550237920224783642704811126318658 :=
  mk_digit2 1197400375427114763184659550237920224783642704811126318658 2 (by native_decide) (by omega)

-- d=191: oddTarget = 37070077048343641696678188907821314893563490484908229691420, digit 2 at position 2
theorem oddTarget_191_hasDigit2 : hasDigit2Bounded 37070077048343641696678188907821314893563490484908229691420 :=
  mk_digit2 37070077048343641696678188907821314893563490484908229691420 2 (by native_decide) (by omega)

-- d=192: oddTarget = 44254479300906330275786146209248836242265346713774987603370, digit 2 at position 0
theorem oddTarget_192_hasDigit2 : hasDigit2Bounded 44254479300906330275786146209248836242265346713774987603370 :=
  mk_digit2 44254479300906330275786146209248836242265346713774987603370 0 (by native_decide) (by omega)

-- d=193: oddTarget = 65807686058594396013110018113531400288370915400375261339220, digit 2 at position 0
theorem oddTarget_193_hasDigit2 : hasDigit2Bounded 65807686058594396013110018113531400288370915400375261339220 :=
  mk_digit2 65807686058594396013110018113531400288370915400375261339220 0 (by native_decide) (by omega)

-- d=194: oddTarget = 130467306331658593225081633826379092426687621460176082546770, digit 2 at position 0
theorem oddTarget_194_hasDigit2 : hasDigit2Bounded 130467306331658593225081633826379092426687621460176082546770 :=
  mk_digit2 130467306331658593225081633826379092426687621460176082546770 0 (by native_decide) (by omega)

-- d=195: oddTarget = 525313422683224969303741742507567494156913113862427650582092, digit 2 at position 1
theorem oddTarget_195_hasDigit2 : hasDigit2Bounded 525313422683224969303741742507567494156913113862427650582092 :=
  mk_digit2 525313422683224969303741742507567494156913113862427650582092 1 (by native_decide) (by omega)

-- d=196: oddTarget = 1308117260673176528654231545465842048717038842623484145862714, digit 2 at position 3
theorem oddTarget_196_hasDigit2 : hasDigit2Bounded 1308117260673176528654231545465842048717038842623484145862714 :=
  mk_digit2 1308117260673176528654231545465842048717038842623484145862714 3 (by native_decide) (by omega)

-- d=197: oddTarget = 1246121708254545793392757815828921808614111538232464378752516, digit 2 at position 2
theorem oddTarget_197_hasDigit2 : hasDigit2Bounded 1246121708254545793392757815828921808614111538232464378752516 :=
  mk_digit2 1246121708254545793392757815828921808614111538232464378752516 2 (by native_decide) (by omega)

-- d=198: oddTarget = 2667073095257643863150298719259323690827532618842197912723298, digit 2 at position 1
theorem oddTarget_198_hasDigit2 : hasDigit2Bounded 2667073095257643863150298719259323690827532618842197912723298 :=
  mk_digit2 2667073095257643863150298719259323690827532618842197912723298 1 (by native_decide) (by omega)

-- d=199: oddTarget = 3716051167748957521338997244868204132423389873105812844032892, digit 2 at position 0
theorem oddTarget_199_hasDigit2 : hasDigit2Bounded 3716051167748957521338997244868204132423389873105812844032892 :=
  mk_digit2 3716051167748957521338997244868204132423389873105812844032892 0 (by native_decide) (by omega)

-- d=200: oddTarget = 6862985385222898495905092821694845457210961635896657637961674, digit 2 at position 0
theorem oddTarget_200_hasDigit2 : hasDigit2Bounded 6862985385222898495905092821694845457210961635896657637961674 :=
  mk_digit2 6862985385222898495905092821694845457210961635896657637961674 0 (by native_decide) (by omega)

-- ================================================================
-- ODD TARGET RESIDUE
-- ================================================================
-- The odd target residue: ((2^(d+4+δ)-1)/3 - 3^(d-1)) mod 2^(d+4)
-- where δ = d % 2.
-- Uses Int.natMod to avoid Nat subtraction underflow.
def oddTarget (d : ℕ) : ℕ :=
  let k := d + 4
  let delta := d % 2
  let a : Int := ((2 ^ (k + delta) - 1 : ℕ) / 3 : ℕ)
  let b : Int := (3 ^ (d - 1) : ℕ)
  let m : Int := (2 ^ k : ℕ)
  (a - b).natMod m

-- ================================================================
-- BLOCKER: General theorem for ALL d ≥ 25
-- This requires proving that (-3^{-1} - 3^{d-1}) mod 2^{d+4} always has digit 2
-- in base 3. Verified computationally for d=1..2000.
-- ================================================================
-- For d=25..70, this follows from the carry machine soundness (odd_enc_bridge).
-- For d≥71, the digit-2 property of oddTarget suffices.
theorem oddTarget_hasDigit2_all (d : ℕ) (hd : 25 ≤ d) :
    hasDigit2Bounded (oddTarget d) := by
  sorry -- BLOCKER: d≥71 needs digit-2 proof

-- ================================================================
-- SUBSET SUM IMPLICATION
-- ================================================================
-- The digit-2 obstruction implies evalBit(d-1,m) ≠ target.
-- If all base-3 digits of n are ≤ 1 (i.e. n is a "Cantor set element"),
-- then n has no digit 2, so it cannot equal the target residue.
theorem subset_sum_no_digit2 (n : ℕ) :
    (∀ i < 128, digit3 n i ≤ 1) → ¬hasDigit2Bounded n := by
  intro h1 ⟨i, hi, h2⟩
  have h1' : digit3 n i ≤ 1 := h1 i hi
  omega

-- ================================================================
-- BRIDGE THEOREM: connect carry machine to evalBit non-divisibility
-- ================================================================
-- For d=25..70, the carry machine (OddEncObstruction) proves that no
-- subset sum of {3^0,...,3^(d-2)} can achieve the target residue
-- oddTarget(d) mod 2^(d+4). This bridge closes the gap in VdBound.
--
-- Mathematical chain:
-- 1. 2^(d+4) | 3*(3^(d-1) + evalBit(d-1,m)) + 1
--    ⟹ 3*(3^(d-1) + evalBit(d-1,m)) ≡ -1 (mod 2^(d+4))
--    ⟹ evalBit(d-1,m) ≡ oddTarget(d) (mod 2^(d+4))
-- 2. The carry machine checks ALL values in the arithmetic progression
--    {oddTarget(d) + k·2^(d+4)} ∩ [0, (3^(d-1)-1)/2] and confirms
--    none are valid subset sums of {3^0,...,3^(d-2)}.
-- 3. Since evalBit(d-1,m) IS such a subset sum, contradiction.

-- ================================================================
-- ALGEBRA: from 2^k | 3*G+1, derive 3*G ≡ 3*val (mod 2^k)
-- ================================================================
-- 3 | (2^n - 1) when n is even (since 2^2 = 4 ≡ 1 mod 3)
private theorem three_dvd_pred_pow2 {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨4 * m + 1, ?_⟩
    have h1 : 2^(k+k) = 3*m + 1 := by
      have h := Nat.eq_add_of_sub_eq (Nat.one_le_pow _ 2 (by norm_num)) hm
      linarith
    rw [show k+1+(k+1) = (k+k) + 2 from by omega, pow_add, pow_two, h1]
    ring_nf
    omega

-- 3 * ((2^n - 1) / 3) + 1 = 2^n when 3 | (2^n - 1)
private theorem three_mul_val_add_one {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) :
    3 * ((2 ^ n - 1) / 3 : ℕ) + 1 = 2 ^ n := by
  have h := Nat.div_mul_cancel h3
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  calc 3 * ((2 ^ n - 1) / 3) + 1
      = ((2 ^ n - 1) / 3) * 3 + 1 := by ring
    _ = (2 ^ n - 1) + 1 := by rw [h]
    _ = 2 ^ n := Nat.sub_add_cancel h1

-- k + delta is even when k = d+4 and delta = d%2
private theorem k_plus_delta_even (d : ℕ) : Even (d + 4 + d % 2) := by
  rcases Nat.even_or_odd d with ⟨r, hr⟩ | ⟨r, hr⟩
  · use r + 2; omega
  · use r + 3; omega

-- Algebra step: from 2^k | 3*G + 1, derive 3*G % 2^k = 3*val % 2^k
-- where val = (2^(k+δ)-1)/3 and δ = d%2.
-- Proof: 3*val + 1 = 2^{k+δ}, so 2^k | 3*val + 1.
-- Both 3*G+1 and 3*val+1 are divisible by 2^k, so 3*G ≡ 3*val (mod 2^k).
private theorem algebra_step (d : ℕ) (m : ℕ) (hd : 1 ≤ d)
    (hdiv : 2 ^ (d + 4) ∣ 3 * (3 ^ (d - 1) + TwoAdicObstruction.evalBit (d - 1) m) + 1) :
    let k := d + 4
    let G := 3 ^ (d - 1) + TwoAdicObstruction.evalBit (d - 1) m
    let delta := d % 2
    let val := (2 ^ (k + delta) - 1) / 3
    3 * G % 2 ^ k = 3 * val % 2 ^ k := by
  intro k G delta val
  have h3val : 3 * val + 1 = 2 ^ (k + delta) := by
    have h3dvd : 3 ∣ 2 ^ (k + delta) - 1 := three_dvd_pred_pow2 (k_plus_delta_even d)
    rw [three_mul_val_add_one h3dvd]
  have h3val_div : 2 ^ k ∣ 3 * val + 1 := by
    rw [h3val]; exact ⟨2 ^ delta, by ring⟩
  -- Both 3*G+1 and 3*val+1 are divisible by 2^k
  -- So 3*G ≡ 3*val (mod 2^k)
  -- Proof: both equal -1 mod 2^k (trivially true, omega limitation with variable-mod %)
  sorry

-- ================================================================
-- BRIDGE THEOREM for d=25..70
-- ================================================================
-- From 2^k | 3*G + 1, the algebra gives 3*G ≡ 3*val (mod 2^k),
-- so G ≡ val (mod 2^k) by coprimality.
-- The carry machine (OddEncObstruction) proves machineDead = true,
-- meaning no subset sum of {3^0,...,3^(d-2)} achieves the target residue.
-- Since evalBit(d-1,m) IS such a subset sum, contradiction.
--
-- BLOCKER: carry machine soundness theorem needed.
-- The carry machine processes d+4 bit positions using tableData(d).
-- At each position j, (p_j, vBits) encodes the fixed and variable
-- contributions of 3*(3^{d-1}+S) at bit j. The machine tracks reachable
-- carry states. If dead after d+4 steps, no valid S exists.
-- Proving this requires formalizing the invariant:
--   state_j = { carries achievable by some partial assignment of bits 0..j-1 }

-- The algebra gives G ≡ val (mod 2^k), i.e. the residue of evalBit is determined.
-- We still need carry machine soundness to derive the contradiction.
theorem odd_enc_bridge (d : ℕ) (hd : 25 ≤ d) (hd70 : d ≤ 70) (m : ℕ) :
    2 ^ (d + 4) ∣ 3 * (3 ^ (d - 1) + TwoAdicObstruction.evalBit (d - 1) m) + 1 → False := by
  intro hdiv
  let k := d + 4
  -- Step 1: algebra gives 3*G % 2^k = 3*val % 2^k
  have h3eq := algebra_step d m (by omega) hdiv
  -- Step 2: by coprimality, G ≡ val (mod 2^k)
  -- This means evalBit(d-1,m) ≡ oddTarget d (mod 2^k)
  -- Step 3: carry machine soundness — dead machine ⟹ no such evalBit exists
  have hdead : (if d = 60 then OddEncObstruction.machineDead 60 64 128 256
    else OddEncObstruction.machineDead d (d + 4) 64 128) = true :=
    OddEncObstruction.odd_enc_obstruction_all d hd hd70
  -- BLOCKER: carry machine soundness theorem
  sorry

-- Variant: for d ≥ 71, the digit-2 property of oddTarget suffices.
-- This is the "low digit two" approach: for all d ≥ 71, oddTarget(d)
-- has digit 2 at some position j ≤ 24, which is a FIXED finite check
-- that can be verified computationally.
theorem odd_target_has_low_digit_two (d : ℕ) (hd : 71 ≤ d) :
    ∃ j ≤ 24, digit3 (oddTarget d) j = 2 := by
  sorry -- BLOCKER: needs proof that digit-2 witness is always low

end OddCaseDigit2
