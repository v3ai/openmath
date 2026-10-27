"""OEIS A135508: x(1)=1, x(n+1) = 2 x(n) + lcm(x(n), n+1),  a(n) = x(n+1)/x(n) - 2
                                     = (n+1) / gcd(x(n), n+1).
McEachen's conjecture (Sep 2025): for prime p with p-2 not prime, a(p-1) = p.

x(n) is astronomically large, so we track v_q(x(n)) for every prime q (capped), which is all
that is needed to compute gcd(x(n), n+1).

Also tests:
  * the OEIS comment "a(n) is always 1 or a prime";
  * the reduction: p | x(p-1)  <=>  a(p-3) = p-2  (for p >= 5).
"""
import sys
import numpy as np
from numba import njit


@njit(cache=True)
def spf_sieve(N):
    spf = np.zeros(N + 1, dtype=np.int32)
    for i in range(2, N + 1):
        if spf[i] == 0:
            for j in range(i, N + 1, i):
                if spf[j] == 0:
                    spf[j] = i
    return spf


@njit(cache=True)
def run(N):
    spf = spf_sieve(N + 3)
    CAP = 60
    val = np.zeros(N + 4, dtype=np.int32)  # v_q(x(n)) for prime q, capped
    a = np.zeros(N + 1, dtype=np.int64)
    # x(1) = 1 : all valuations zero
    for n in range(1, N + 1):
        m = n + 1
        # a(n) = prod over q^k || m of q^{max(0, k - v_q(x))}
        an = 1
        t = m
        while t > 1:
            q = spf[t]
            k = 0
            while t % q == 0:
                t //= q
                k += 1
            ex = k - val[q]
            for _ in range(ex):
                an *= q
        a[n] = an
        # x(n+1) = x(n) * (2 + a(n))
        f = 2 + an
        while f > 1:
            q = spf[f]
            while f % q == 0:
                f //= q
                if val[q] < CAP:
                    val[q] += 1
    return a, spf


if __name__ == "__main__":
    N = int(sys.argv[1])
    a, spf = run(N)
    isprime = lambda k: k >= 2 and spf[k] == k
    print("first terms:", list(a[1:41]))
    # OEIS comment: only 1's and primes
    bad = [n for n in range(1, N + 1) if a[n] != 1 and not isprime(int(a[n]))]
    print("a(n) not 1/prime for n <=", N, ":", len(bad), bad[:10])
    # McEachen's conjecture
    viol = []
    twin_appear = []
    for p in range(3, N + 2):
        if not isprime(p):
            continue
        if not isprime(p - 2):
            if a[p - 1] != p:
                viol.append(p)
        else:
            if a[p - 1] == p:
                twin_appear.append(p)
    print("conjecture violations for primes p <=", N + 1, ":", len(viol), viol[:10])
    print("primes p with p-2 prime that still appear at a(p-1):", twin_appear[:10])
    # reduction check: for primes p >= 5,  p | x(p-1)  <=>  a(p-3) = p-2  <=>  a(p-1) != p
    red_bad = 0
    for p in range(5, N + 2):
        if isprime(p) and ((a[p - 1] != p) != (a[p - 3] == p - 2)):
            red_bad += 1
    print("reduction mismatches:", red_bad)
