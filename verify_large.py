def main():
    print("Verifying Erdős conjecture at scale...")
    print("Checking n from 9 to 100,000\n")
    
    counterexamples = []
    
    val = 2 ** 9
    
    for n in range(9, 100001):
        x = val
        has_two = False
        while x:
            if x % 3 == 2:
                has_two = True
                break
            x //= 3
        
        if not has_two:
            counterexamples.append(n)
            print(f"COUNTEREXAMPLE: n={n}")
        
        val *= 2
    
    print(f"\nChecked n from 9 to 100,000")
    if counterexamples:
        print(f"Counterexamples: {counterexamples}")
    else:
        print("No counterexamples found - conjecture verified for n in [9, 100000]")

if __name__ == "__main__":
    main()
