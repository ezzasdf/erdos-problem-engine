def main():
    print("Verifying Erdős conjecture: 2^n contains digit 2 in ternary for n > 8\n")
    
    counterexamples = []
    verified = 0
    
    val = 2 ** 9  # start at n=9
    
    for n in range(9, 5001):
        t = []
        x = val
        if x == 0:
            t = "0"
        else:
            while x:
                t.append(str(x % 3))
                x //= 3
            t = ''.join(reversed(t))
        
        has_two = '2' in t
        
        if not has_two:
            counterexamples.append(n)
            print(f"n={n}: 2^{n} ternary = {t} (NO DIGIT 2!)")
        
        verified += 1
        val *= 2  # next power of 2
    
    print(f"\nResults:")
    print(f"Checked n from 9 to 5000 (4992 values)")
    print(f"Verified: {verified}")
    print(f"Counterexamples found: {len(counterexamples)}")
    
    if counterexamples:
        print(f"\nCounterexamples: {counterexamples}")
    else:
        print("\nNo counterexamples found - conjecture holds for n in [9, 5000]")

    print("\n--- Sample ternary expansions ---")
    v = 1
    for n in range(0, 21):
        t = []
        x = v
        while x:
            t.append(str(x % 3))
            x //= 3
        t = ''.join(reversed(t))
        has_two = '2' in t
        marker = "" if has_two else " <-- NO 2!"
        print(f"2^{n:2d} = {v:>10}, ternary = {t:>20}{marker}")
        v *= 2

if __name__ == "__main__":
    main()
