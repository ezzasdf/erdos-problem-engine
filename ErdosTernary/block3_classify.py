import time
from collections import Counter

def generate_no2_set(n_digits):
    no2 = set()
    for i in range(2 ** n_digits):
        val = 0
        temp = i
        for _ in range(n_digits):
            val = val * 3 + (temp & 1)
            temp >>= 1
        no2.add(val)
    return no2

def main():
    P = 2 * 3**14
    mod_3_15 = 3**15
    mod_3_30 = 3**30
    mod_3_45 = 3**45
    mod_3_60 = 3**60

    pow2_P_30 = pow(2, P, mod_3_30)
    pow2_P_45 = pow(2, P, mod_3_45)
    pow2_P_60 = pow(2, P, mod_3_60)

    no2 = generate_no2_set(15)

    for s in [0, 2, 8]:
        print(f"\n{'='*60}")
        print(f"Block 3 analysis for s = {s}")
        print(f"{'='*60}")

        pow2_s_60 = pow(2, s, mod_3_60)

        # Collect block-2 exceptional residues
        t0 = time.time()
        exc2 = []
        current45 = pow(2, s, mod_3_45)
        current60_for_b2 = pow2_s_60
        
        # We need to find block-2 exceptions
        # Iterate through all r, tracking both block-1 and block-2
        b1_exc_set = set()
        b2_exc_list = []
        
        current30 = pow(2, s, mod_3_30)
        current45 = pow(2, s, mod_3_45)
        current60 = pow2_s_60
        
        for r in range(1, mod_3_15):
            current30 = (current30 * pow2_P_30) % mod_3_30
            current45 = (current45 * pow2_P_45) % mod_3_45
            current60 = (current60 * pow2_P_60) % mod_3_60
            
            block1 = (current30 // 3**15) % 3**15
            if block1 in no2:
                b1_exc_set.add(r)
                block2 = (current45 // 3**30) % 3**15
                if block2 in no2:
                    b2_exc_list.append((r, current60))
        
        t1 = time.time()
        print(f"Block-2 exceptional: {len(b2_exc_list)} ({t1-t0:.1f}s)")
        
        # Now check block 3 for each block-2 exception
        t0 = time.time()
        b3_caught = 0
        b3_exc = 0
        b3_exc_residues = []
        b3_witnesss = []
        
        for r, val60 in b2_exc_list:
            block3 = (val60 // 3**45) % 3**15
            if block3 not in no2:
                b3_caught += 1
                temp = block3
                for pos in range(15):
                    if temp % 3 == 2:
                        b3_witnesss.append(45 + pos)
                        break
                    temp //= 3
            else:
                b3_exc += 1
                b3_exc_residues.append(r)
        
        t1 = time.time()
        print(f"Block-3 caught (digit 2 in pos 45..59): {b3_caught}")
        print(f"Block-3 exceptional: {b3_exc}")
        print(f"Time: {t1-t0:.1f}s")
        
        if b3_witnesss:
            wc = Counter(b3_witnesss)
            print(f"Block-3 witness positions: {dict(sorted(wc.items()))}")
        
        if b3_exc_residues:
            print(f"Block-3 exceptional residues ({len(b3_exc_residues)}):")
            print(f"  {b3_exc_residues}")
        else:
            print("ALL residues caught by block 3!")

    # Also verify the injectivity: order of 2^P mod 3^30
    print(f"\n{'='*60}")
    print(f"Injectivity check: (2^P)^(3^14) mod 3^30 = {pow(pow(2, P, mod_3_30), 3**14, mod_3_30)}")
    print(f"Order of 2^P mod 3^30 is exactly 3^15: {pow(pow(2, P, mod_3_30), 3**14, mod_3_30) != 1}")

if __name__ == "__main__":
    main()
