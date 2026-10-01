import sys


def _base3(m: int) -> list:
    v = []
    while m > 0:
        v.append(m % 3)
        m //= 3
    return v


def stream_digits(max_n: int, checkpoint: int = 2000) -> None:
    """Independent streaming base-3 doubling, cross-checked against pow(2, n).

    Every n: low-order 20 digits checked against 2^n mod 3^20 (cheap).
    Checkpoints: full digit string checked against pow(2, n) base-3.

    NOTE: range capped at a feasible pure-Python scale (default 10^4); the
    Rust --verify covers 10^5 with the same two checks.
    """
    modk = 3 ** 20
    digits = [1]
    m = 1  # 2^n mod 3^20
    for n in range(0, max_n + 1):
        k = min(len(digits), 20)
        low = []
        r = m
        for _ in range(k):
            low.append(r % 3)
            r //= 3
        assert digits[:k] == low, f"low-digit mismatch at n={n}"
        if n % checkpoint == 0:
            full = _base3(pow(2, n))
            assert digits == full, f"full mismatch at n={n}"
        c = 0
        for i in range(len(digits)):
            s = 2 * digits[i] + c
            digits[i] = s % 3
            c = s // 3
        if c:
            digits.append(c)
        m = (2 * m) % modk
    print(f"python cross-check ok through n={max_n}")


if __name__ == "__main__":
    stream_digits(int(sys.argv[1]) if len(sys.argv) > 1 else 10_000)