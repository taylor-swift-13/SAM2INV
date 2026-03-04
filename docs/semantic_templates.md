# Semantic Template Catalog — Loop Factory

This document describes all semantic templates in `loop_factory.py`.
Each template has a **named invariant**, a **code pattern**, **source files** it generalizes,
and a **Frama-C verifiability** note.

Templates are grouped by series:
- **L-series** (L1–L20): Linear arithmetic invariants, from `src/input/linear/`
- **N-series** (N1–N14): Nonlinear/polynomial invariants, from `src/input/NLA_lipus/`
- **X-series** (X1–X20): Novel templates with no direct benchmark analog
- **ML-series** (ML1–ML8): Multi-loop patterns pairing two single-loop templates

Complexity levels: **simple** / **medium** / **complex** are controlled by DSL parameters
(`assign_fuel`, `ifelse_fuel`, constant choices), not by template selection.

---

## Frama-C Verifiability Summary

| Category | Example | Status |
|---|---|---|
| Linear arithmetic | `x + y == C`, `0 <= c <= MAX` | ✅ Fully automatic (WP + Alt-Ergo) |
| Low-degree polynomial | `product == a*b`, `z*w >= p*p` | ✅ WP + Z3 (nonlinear plugin) |
| Cubic/quartic polynomial | `x == n^3`, `6*x == 2n³+3n²+n` | ✅ WP + Z3 |
| Bezout determinant | `p*s - r*q == 1` | ✅ Polynomial equality |
| GCD value | `gcd(a,b) == gcd(x,y)` | ❌ No `\gcd` in ACSL |
| Exact power | `z == 2^n` | ❌ Exponential non-linear integer |
| Alternating sign | Cassini: `a²-ab-b² == (-1)^k` | ❌ Sign-alternating |

---

## L-Series: Linear Templates

### L1 · Affine Accumulator
**Invariant**: `x == Σ_{t=0}^{i-1} f(t)` for affine f
**Sources**: linear/1, 2, 172
**Frama-C**: ✅

```c
// Simple: triangular sum
int i=0, x=0;
while (i < n) { x = x + i; i = i + 1; }
// assert 2*x == i*(i-1)

// Medium: constant stride
int i=0, x=0;
while (i < n) { x = x + 3; i = i + 1; }
// assert x == 3 * i

// Complex: two accumulators
int i=0, x=0, y=0;
while (i < n) { x = x + i; y = y + 2*i + 1; i = i + 1; }
// assert y == i*i
```

---

### L2 · Simple Countdown
**Invariant**: `x + y == x_init`
**Sources**: linear/25, 100, 101
**Frama-C**: ✅

```c
// Simple
int x = n;
while (x > 0) { x = x - 1; }
// assert x == 0

// Medium: complementary pair
int x = n, y = 0;
while (x > 0) { x = x - 1; y = y + 1; }
// assert y == n
```

---

### L3 · Proportional Stride
**Invariant**: `j == k * i`
**Sources**: linear/154
**Frama-C**: ✅

```c
// Simple: k=2
int i=0, j=0;
while (i < n) { j = j + 2; i = i + 1; }
// assert j == 2 * i

// Medium: k is parameter
int i=0, j=0;
while (i < n) { j = j + k; i = i + 1; }
// assert j == k * i
```

---

### L4 · Linear Conservation Law
**Invariant**: `a + b == C` (constant sum) or `a - b == C` (constant difference)
**Sources**: linear/10, 316
**Frama-C**: ✅

```c
// Simple: both grow at same rate (same "cost")
int x=0, y=0, i=0;
while (i < n) { x = x + 2; y = y + 2; i = i + 1; }
// assert x == y

// Medium: equal-and-opposite branch
int x=0, y=0, i=0;
while (i < n) {
  if (i % 2 == 0) { x = x + 1; y = y - 1; }
  else            { x = x - 1; y = y + 1; }
  i = i + 1;
}
// assert x + y == 0
```

---

### L5 · Countdown Triple (3-Way Conservation)
**Invariant**: `lo + hi == 2 * mid_init`
**Sources**: linear/145
**Frama-C**: ✅

```c
// Simple: unit steps
int lo=0, hi=2*m, mid=m;
while (mid > 0) { lo = lo+1; hi = hi-1; mid = mid-1; }
// assert lo == hi

// Medium: step=2
int lo=0, hi=4*m, mid=m;
while (mid > 0) { lo = lo+2; hi = hi-2; mid = mid-1; }
// assert lo == hi
```

---

### L6 · Snapshot Chase (Synchronized Decrement)
**Invariant**: `a - b == a_init - b_init`
**Sources**: linear/124, 125, 160, 270
**Frama-C**: ✅

```c
// Simple: unit step, single pair
int i=x, j=y;
while (x != 0) { x = x - 1; y = y - 1; }
// assert (i == j) ==> (y == 0)

// Medium: parameterized step
int snap_a=x, snap_b=y;
while (x > 0) { x = x - d; y = y - d; }
// assert x - y == snap_a - snap_b
```

---

### L7 · Parity Flip-Flop
**Invariant**: `|i - j| <= 1`
**Sources**: linear/176
**Frama-C**: ✅

```c
// Simple: boolean flag alternation
int n=0, b=1, i=x, j=y;
while (n < 2*k) {
  n = n + 1;
  if (b == 1) { b = 0; i = i + 1; }
  else        { b = 1; j = j + 1; }
}
// assert i == j

// Medium: using n%2 directly
int n=0, i=x, j=y;
while (n < 2*k) {
  n = n + 1;
  if (n % 2 == 1) { i = i + 1; }
  else            { j = j + 1; }
}
// assert i == j
```

---

### L8 · Saturation Guard
**Invariant**: `0 <= c <= MAX`
**Sources**: linear/35, 36, 37, 50, 55
**Frama-C**: ✅

```c
// Simple: MAX=4
int c=0, i=0;
while (i < n) {
  if (i % 2 == 0) { if (c != 4) { c = c + 1; } }
  else            { if (c == 4) { c = 1; } }
  i = i + 1;
}
// assert 0 <= c && c <= 4

// Medium: parameterized MAX
int c=0, i=0;
while (i < n) {
  if (i % 5 != 4) { if (c != MAX) { c = c + 1; } }
  else            { if (c == MAX) { c = 1; } }
  i = i + 1;
}
// assert 0 <= c && c <= MAX
```

---

### L9 · Sliding Window / Bounded Accumulation
**Invariant**: `z == base + c`
**Sources**: linear/75
**Frama-C**: ✅

```c
// Simple
int c=0, z=36*y;
while (c < 36) { z = z + 1; c = c + 1; }
// assert z == 36*y + 36

// Medium: LIMIT from parameter
int c=0, z=m*n;
while (c < m) { z = z + 1; c = c + 1; }
// assert z == m*n + c
```

---

### L10 · Piecewise Multi-Rate
**Invariant**: branch-dependent linear bound
**Sources**: linear/150
**Frama-C**: ✅

```c
// Simple: 2-branch piecewise
int x=0, y=0, i=0;
while (i < n) {
  if (x >= 4) { x = x+1; y = y+1; }
  else        { x = x+1; y = y+100; }
  i = i + 1;
}
```

---

### L11 · Triple Modular Step
**Invariant**: `j + k == i`
**Sources**: linear/300, 316
**Frama-C**: ✅

```c
// Simple: step=1, parity split
int i=0, j=0, k=0;
while (i < n) {
  i = i + 1;
  if (i % 2 != 0) { j = j + 1; }
  else            { k = k + 1; }
}
// assert j + k == i

// Medium: step=3
int i=0, j=0, k=0;
while (i < n) {
  i = i + 3;
  if (i % 2 != 0) { j = j + 3; }
  else            { k = k + 3; }
}
```

---

### L12 · Monotone Increment (Lower Bounded)
**Invariant**: `x >= x_init`
**Sources**: linear/101, 201
**Frama-C**: ✅

```c
// Simple
int x = 0;
while (x < n) { x = x + 1; }
// assert x >= n

// Medium: conditional step
int x=-3, i=0;
while (i < k) {
  if (x < 1) { x = x + 2; }
  else        { x = x + 1; }
  i = i + 1;
}
// assert x >= -3
```

---

### L13 · Binary Toggle / One-Way Latch
**Invariant**: `x <= 1`
**Sources**: linear/260
**Frama-C**: ✅

```c
// Simple
int x=0, i=0;
while(1) {
  i = i + 1;
  if (x == 0) { x = 1; }
  if (x == 1 || i >= n) break;
}
// assert x <= 1

// Medium: two latches
int a=0, b=0, i=0;
while (i < n) {
  if (a == 0)           { a = 1; }
  if (a == 1 && b == 0) { b = 1; }
  i = i + 1;
}
// assert b <= a
```

---

### L14 · Cache Coherence / Resource Conservation
**Invariant**: `sum of all state counts == C`
**Sources**: linear/212–215
**Frama-C**: ✅

```c
// Simple: 2 states (free + owned == n)
int free=n, owned=0, i=0;
while (i < m) {
  if (i % 2 == 0 && free > 0) { free = free-1; owned = owned+1; }
  else if (owned > 0)          { owned = owned-1; free = free+1; }
  i = i + 1;
}
// assert free + owned == n

// Medium: 3 states (free / shared / exclusive)
int fr=n, sh=0, ex=0, i=0;
while (i < m) {
  if      (i%3==0 && fr>0) { fr--; sh++; }
  else if (i%3==1 && sh>0) { sh--; ex++; }
  else if (ex>0)           { ex--; fr++; }
  i = i + 1;
}
// assert fr + sh + ex == n
```

---

### L15 · Multi-Countdown Parallel
**Invariant**: at least one counter reaches 0
**Sources**: linear/200
**Frama-C**: ✅

```c
// Simple: 2 counters alternating
int x1=n, x2=m, i=0;
while (x1 > 0 && x2 > 0) {
  if (i % 2 == 0) { x1 = x1 - 1; }
  else            { x2 = x2 - 1; }
  i = i + 1;
}
// assert x1 == 0 || x2 == 0

// Medium: 3 counters
int x1=a, x2=b, x3=c, i=0;
while (x1 > 0 && x2 > 0 && x3 > 0) {
  if      (i%3==0) { x1 = x1-1; }
  else if (i%3==1) { x2 = x2-1; }
  else             { x3 = x3-1; }
  i = i + 1;
}
// assert x1==0 || x2==0 || x3==0
```

---

### L16 · Min-Tracking Update
**Invariant**: `y >= z` (y tracks running minimum)
**Sources**: linear/3
**Frama-C**: ✅

```c
int y=n, z=m, x=0;
while (x < 5) { x = x+1; if (z <= y) { y = z; } }
// assert z >= y  (y converged to min)
```

---

### L17 · Geometric Doubling Bound
**Invariant (verifiable)**: `z > n` (linear lower bound; NOT `z == 2^n` — exponential)
**Frama-C note**: Use `z > n` rather than `z == 2^n`. Exponential exact equality requires
a non-linear integer exponentiation predicate that automated provers cannot verify.

```c
// Simple: linear bound only
int z=1, n=0;
while (n < k) { z=z*2; n++; }
// assert z > n   [provable; NOT: z == (1<<n)]
```

---

### L18 · Sawtooth Modular Counter
**Invariant**: `0 <= c < PERIOD`
**Frama-C**: ✅

```c
// Simple: PERIOD=4
int c=0, n=0;
while (n < bound) { c = (c + 1) % 4; n++; }
// assert 0 <= c && c < 4

// Medium: parameterized
int c=0, n=0;
while (n < bound) { c = (c + 1) % p; n++; }
// assert 0 <= c && c < p
```

---

### L19 · Linked Countdown
**Invariant**: `x2 >= 0` while `x1` decreases
**Sources**: linear/130
**Frama-C**: ✅

```c
// Simple: two linked counters
int x1=n, x2=m;  // n >= m required
while (x1 > 0) {
  if (x2 > 0) { x1--; x2--; }
  else        { x1--; }
}
// assert x2 >= 0
```

---

### L20 · Decaying Stride
**Invariant**: `i + k <= k0 + 2` where `k0` is initial k; stride decreases each step
**Sources**: linear/250
**Frama-C**: ✅

```c
// Simple
int i=1, j=1, k=k0;
while (i < n) { i=i+1; j=j+k; k=k-1; }
// assert i + k <= k0 + 2

// Medium: countdown from large stride
int step=n, acc=0, i=0;
while (step > 0) { acc=acc+step; step=step-1; i=i+1; }
// assert acc == n*(n+1)/2 && step == 0
```

---

## N-Series: Nonlinear / Polynomial Templates

### N1 · Polynomial Finite Differences
**Invariant**: `x == n^d` via cascaded differences
**Sources**: NLA/1
**Frama-C**: ✅ (low-degree polynomial, WP+Z3)

```c
// Simple (quadratic): assert x == c*c
int x=0, y=1, c=0;
while (c < k) { c++; x=x+y; y=y+2; }
// assert x == c*c

// Medium (cubic): assert x == c*c*c
int x=0, y=1, z=6, c=0;
while (c < k) { c++; x=x+y; y=y+z; z=z+6; }
```

---

### N2 · Triangular Sum (Power Sum k=1)
**Invariant**: `2 * x == c * (c + 1)`
**Sources**: NLA/15
**Frama-C**: ✅

```c
int y=0, x=0, c=0;
while (c < k) { c++; y++; x = x + y; }
// assert 2*x == k*(k+1)
```

---

### N3 · Square Sum (Power Sum k=2)
**Invariant**: `6*x == 2*c^3 + 3*c^2 + c`
**Sources**: NLA/16
**Frama-C**: ✅

```c
int y=0, x=0, c=0;
while (c < k) { c++; y++; x = x + y*y; }
// assert 6*x - 2*k*k*k - 3*k*k - k == 0
```

---

### N4 · Higher Power Sums (k=3,4,5)
**Invariant**: Faulhaber closed-form polynomial
**Sources**: NLA/17 (d=3), NLA/18 (d=4), NLA/19 (d=5)
**Frama-C**: ✅ (cubic and quartic)

```c
// d=3 (cubic sum): 4*x == k^4 + 2k^3 + k^2
int y=0, x=0, c=0;
while (c < k) { c++; y++; x = x + y*y*y; }
```
DSL selects d: simple=3, medium=4, complex=5.

---

### N5 · Quotient-Remainder Division
**Invariant**: `x == y * q + r` and `0 <= r < y`
**Sources**: NLA/2, 3, 4, 12
**Frama-C**: ✅

```c
// Simple (remainder only)
int q=0, r=0;
while (x > y*q + r) {
  if (r == y-1) { r=0; q=q+1; }
  else          { r=r+1; }
}
// assert r == x % y

// Medium (quotient): assert q == x/y
// Complex (countdown): NLA/12 style countdown variant
```

---

### N6 · Extended Euclidean / Bezout
**Invariant**: `p*s - r*q == 1` (Bezout determinant)
**Sources**: NLA/5, 6, 7, 8
**Frama-C**: ✅ (polynomial equality)

```c
// Simple: just GCD convergence
int a=x, b=y;
while (a != b) {
  if (a > b) { a = a - b; }
  else       { b = b - a; }
}
// assert a == b

// Complex: full 4-coefficient Bezout
int a=x,b=y,p=1,q=0,r=0,s=1;
while (a!=b) {
  if (a>b) { a=a-b; p=p-r; q=q-s; }
  else     { b=b-a; r=r-p; s=s-q; }
}
// assert p*s - r*q == 1
```

---

### N7 · Geometric Series with Affine Correction
**Invariant**: `z*x - x + a - a*z*y == 0`
**Sources**: NLA/10, 11
**Frama-C**: ✅

```c
// Simple: a=1
int x=1, y=1, c=1;
while (c < k) { c++; x=x*z+1; y=y*z; }
// assert 1 + x*z - x - z*y == 0

// Medium: a as parameter
int x=a, y=1, c=1;
while (c < k) { c++; x=x*z+a; y=y*z; }
// assert z*x - x + a - a*z*y == 0
```

---

### N8 · Integer Square Root (Odd-Sum Sieve)
**Invariant**: `r^2 <= A`
**Sources**: NLA/20, 36, 43, 44
**Frama-C**: ✅

```c
// Simple: basic sieve
int r=0, x=a/2;
while (x > r) { x=x-r; r=r+1; }
// assert (r-1)*(r-1) <= a

// Medium: with odd-number tracking
int a=0, s=1, t=1;
while (s <= n) { a=a+1; t=t+2; s=s+t; }
// assert n < (a+1)*(a+1)
```

---

### N9 · Cauchy-Schwarz Accumulation
**Invariant**: `z*w >= p*p`
**Sources**: NLA/29, 30
**Frama-C**: ✅

```c
// Simple: x, y fixed; n decrements
int z=0, w=0, p=0, n=N;
while (n > 0) { z=z+x*x; w=w+y*y; p=p+x*y; n--; }
// assert z*w >= p*p
```

---

### N10 · Russian Peasant Multiplication
**Invariant**: `z + x*y == a*b`
**Sources**: NLA/14
**Frama-C**: ✅

```c
int x=a, y=b, z=0;
while (y != 0) {
  if (y % 2 == 1) { z=z+x; y=y-1; }
  x=2*x; y=y/2;
}
// assert z == a*b
```

---

### N11 · Product by Repeated Addition
**Invariant**: `product == a * i`
**Sources**: NLA/31, 40, 42
**Frama-C**: ✅

```c
// Simple
int product=0, i=0;
while (i < b) { product=product+a; i++; }
// assert product == a*b

// Medium: two products in parallel
int p=0, q=0, i=0;
while (i < b) { p=p+a; q=q+2*a; i++; }
// assert p == a*b && q == 2*a*b
```

---

### N12 · Squared Invariant Maintenance
**Invariant**: `x == y*y`
**Sources**: NLA/21, 22
**Frama-C**: ✅

```c
// Simple: exact squared maintenance
int x=0, y=0, i=0;
while (i < k) { y=y+1; x=y*y; i=i+1; }
// assert x == y*y

// Complex: while(1)+break when x exceeds bound
int x=0, y=0;
while(1) { y=y+1; x=y*y; if (x > limit) break; }
// assert x == y*y at break
```

---

### N13 · Affine Geometric Series
**Invariant**: `z == w * b` (one-step-ahead ratio)
**Sources**: NLA/25
**Frama-C**: ✅

```c
// Simple: fixed multiplier b
int w=a, z=a*b, i=0;
while (i < k) { w=w*b; z=z*b; i=i+1; }
// assert z == w*b

// Complex: while(1)+break when w exceeds limit
int w=a, z=a*x;
while(1) { w=w*x; z=z*x; if (w > limit) break; }
// assert z == w*x
```

---

### N14 · Quadratic Piecewise (Simplified)
**Invariant**: `d grows monotonically`; swap variant: `r + t` bounded
**Sources**: NLA/50, 51
**Frama-C**: ⚠️ (asserting structural termination only)

```c
// Simple: 2-branch piecewise swap
int r=A, t=0, d=2;
while (d <= s) {
  if (2*r < d) { t=r; r=2*r+d; d=d+2; }
  else         { t=r; r=2*r-d; d=d+2; }
}
// assert d > s  (terminates)
```

---

## X-Series: Novel Templates

### X1 · Geometric Growth Bound
**Invariant (verifiable)**: `z > n` (linear bound; NOT `z == base^n`)
**Frama-C note**: Exact exponential equality is non-linear and cannot be verified automatically.
Assert the observable linear consequence instead.

```c
// Simple
int z=1, n=0;
while (n < k) { z=z*2; n++; }
// assert z > n  [provable] NOT: z == (1<<n)
```

---

### X2 · GCD Convergence (Structural Only)
**Invariant (verifiable)**: `a >= 1 && b >= 1 && a + b <= x + y` (monotone sum decrease)
**Frama-C note**: `gcd(a,b) == gcd(x,y)` requires a custom ACSL predicate. Assert
the structural property: both stay positive and their sum strictly decreases.

```c
// Simple
int a=x, b=y;
while (a != b) {
  if (a > b) { a=a-b; }
  else       { b=b-a; }
}
// assert a >= 1 && b >= 1 && a == b
// NOT: assert a == gcd(x,y)
```

---

### X3 · Bisection Narrowing
**Invariant**: `hi - lo` strictly decreasing; `lo <= hi`
**Frama-C**: ✅

```c
// Simple: fixed target
int lo=0, hi=n;
while (hi > lo + 1) {
  int mid = (lo+hi)/2;
  if (mid*mid > n) { hi=mid; }
  else             { lo=mid; }
}
// assert lo*lo <= n && n < hi*hi
```

---

### X4 · Coupled Counter-Accumulator
**Invariant**: `2*acc == ctr*(ctr-1)`
**Frama-C**: ✅

```c
// Simple: triangular explicit form
int ctr=0, acc=0, prev=0;
while (ctr < n) { prev=ctr; ctr++; acc=acc+prev; }
// assert 2*acc == ctr*(ctr-1)

// Complex: acc = 2^ctr - 1
int ctr=0, acc=0;
while (ctr < n) { ctr++; acc=2*acc+1; }
// assert acc == (1 << ctr) - 1   [requires bitshift predicate]
```

---

### X5 · Bouncing Counter
**Invariant**: `lo <= x <= hi`
**Frama-C**: ✅

```c
// Simple
int x=lo, d=1, i=0;
while (i < n) {
  if (x >= hi) { d=-1; }
  if (x <= lo) { d=1; }
  x=x+d;
  i=i+1;
}
// assert lo <= x && x <= hi

// Medium: while(1)+break after k bounces
int x=lo, d=1, bounces=0;
while(1) {
  if (x >= hi) { d=-1; bounces=bounces+1; }
  if (x <= lo && bounces > 0) { d=1; bounces=bounces+1; }
  x=x+d;
  if (bounces >= k) break;
}
// assert lo <= x && x <= hi
```

---

### X6 · Quadratic Residual / Newton Step
**Invariant**: `r*r <= A && (r+1)*(r+1) > A` (tight integer sqrt bounds)
**Frama-C**: ✅

```c
int r=0, rem=A;
while (rem > r) { rem=rem-r; r++; }
// assert r*r <= A  (implicit upper bound from loop exit)
```

---

### X7 · Carry-Propagation Accumulator
**Invariant (verifiable)**: `result >= a*n` (linear lower bound)
**Frama-C note**: Full form `result == a*(z^n-1)/(z-1)` uses exponential.
Assert the one-step algebraic recurrence: `z * prev_result + a == result`.

```c
// Simple: assert result >= n (linear bound)
int result=0, n=0;
while (n < k) { result=result*2+1; n++; }
// assert result >= n  [NOT: result == (1<<k)-1]

// Medium: assert result >= a*n
int result=0, n=0;
while (n < k) { result=result*z+a; n++; }
// assert result >= a*n
```

---

### X8 · Dual-Phase Recurrence
**Invariant (verifiable)**: `a >= b && b >= 0` (structural dominance)
**Frama-C note**: Cassini identity `a²-ab-b²==(-1)^k` alternates sign — not provable automatically.
Assert the stable dominance property instead.

```c
// Simple
int a=n, b=1, c=0;
while (c < k) { int t=a; a=a+b; b=t; c++; }
// assert a >= b && b >= 1  [NOT: Cassini identity]
```

---

### X9 · Accumulated Difference
**Invariant**: `a - b == a_init - b_init` (gap preserved)
**Frama-C**: ✅

```c
// Simple: both increment by same p
int a=x, b=y, i=0;
while (i < n) { a=a+p; b=b+p; i=i+1; }
// assert a - b == x - y

// Medium: conditional direction (gap still preserved)
int a=x, b=y, i=0;
while (i < n) {
  if (i % 2 == 0) { a=a+3; b=b+3; }
  else            { a=a-1; b=b-1; }
  i=i+1;
}
// assert a - b == x - y
```

---

### X10 · Prefix-Sum with Running Count
**Invariant**: `2*sum == i*(i-1)` and `sum == i*i` (odd-number form)
**Frama-C**: ✅

```c
// Simple: triangular
int sum=0, i=0;
while (i < n) { sum=sum+i; i=i+1; }
// assert 2*sum == n*(n-1)

// Medium: sum of odd numbers = perfect square
int sum=0, i=0;
while (i < n) { sum=sum+2*i+1; i=i+1; }
// assert sum == n*n
```

---

### X11 · Odd-Sum Perfect Square
**Invariant**: `sum == i*i`
**Frama-C**: ✅ (nonlinear, WP+Z3)

```c
// Simple
int sum=0, odd=1, i=0;
while (i < n) { sum=sum+odd; odd=odd+2; i=i+1; }
// assert sum == n*n

// Medium: explicit formula
int sum=0, i=0;
while (i < n) { sum=sum+(2*i+1); i=i+1; }
// assert sum == i*i
```

---

### X12 · Modular Equality Race
**Invariant**: `a % m == b % m`
**Frama-C**: ✅

```c
// Simple: both start at same residue, advance by m
int a=r, b=r, i=0;
while (i < n) { a=a+m; b=b+m; i=i+1; }
// assert a % m == b % m

// Medium: different initial offsets by m
int a=r, b=r+m, i=0;
while (i < n) { a=a+m; b=b+m; i=i+1; }
// assert a % m == b % m == r % m
```

---

### X13 · Convergent Pair (Meet in Middle)
**Invariant**: `lo <= hi`; converging until they meet
**Frama-C**: ✅

```c
// Simple: symmetric convergence
int lo=0, hi=n;
while (lo < hi) { lo=lo+1; hi=hi-1; }
// assert lo >= hi && lo + hi >= n - 1

// Complex: while(1)+break at meeting point
int lo=a, hi=b;
while(1) { lo=lo+1; hi=hi-1; if (lo >= hi) break; }
// assert lo + hi == a + b  (sum conserved)
```

---

### X14 · Interval Shrinking
**Invariant**: `hi - lo` strictly decreasing and `>= 0`
**Frama-C**: ✅

```c
// Simple: lo advances faster than hi retreats
int lo=0, hi=n;
while (hi - lo > 1) { lo=lo+2; hi=hi-1; }
// assert hi - lo <= 1

// Medium: alternating shrink
int lo=0, hi=n, i=0;
while (hi > lo) {
  if (i % 2 == 0) { hi = hi - 1; }
  else            { lo = lo + 1; }
  i = i + 1;
}
// assert lo == hi
```

---

### X15 · Diagonal Walk
**Invariant**: `i + j == n`
**Frama-C**: ✅

```c
// Simple
int i=0, j=n;
while (i < n) { i=i+1; j=j-1; }
// assert i + j == n

// Medium: weighted diagonal
int i=0, j=2*n;
while (i < n) { i=i+2; j=j-2; }
// assert i + j == 2*n
```

---

### X16 · Carry-Chain Adder
**Invariant**: `a + b == a_init + b_init`; after loop `b < m`
**Frama-C**: ✅

```c
// Simple: transfer units of m at a time
int a=0, b=n, m=k;
while (b >= m) { a=a+m; b=b-m; }
// assert a + b == n && b < m
```

---

### X17 · Harmonic-Like Step Reduction
**Invariant (linear)**: `steps <= n`
**Frama-C note**: True bound is O(log n); assert linear upper bound `steps <= n`.

```c
// Simple: halving steps bounded by n
int x=n, steps=0;
while (x > 0) { x=x/2; steps=steps+1; }
// assert steps <= n
```

---

### X18 · Matrix Trace Preservation
**Invariant**: `p + s == p_init + s_init` (diagonal sum preserved)
**Frama-C**: ✅

```c
// Simple: p increases, s decreases by same amount
int p=a, s=d, i=0;
while (i < n) { p=p+1; s=s-1; i=i+1; }
// assert p + s == a + d
```

---

### X19 · Rolling Sum Window
**Invariant**: `rolling == curr + prev`
**Frama-C**: ✅

```c
// Simple: rolling sum of last 2 values
int prev=0, curr=1, rolling=1, i=2;
while (i < n) {
  int next=curr+1;
  rolling = rolling + next - prev;
  prev=curr; curr=next;
  i=i+1;
}
// assert rolling == curr + prev
```

---

### X20 · Amortized Credit Counter
**Invariant**: `work + credit <= total`
**Frama-C**: ✅

```c
// Simple: spend 1 credit per step
int credit=n, work=0;
while (credit > 0) { credit=credit-1; work=work+1; }
// assert work == n && credit == 0

// Medium: spend 2, get 1 back every 3 steps
int credit=n, work=0, i=0;
while (credit >= 2) {
  credit=credit-2; work=work+1;
  if (i % 3 == 0 && credit < n) { credit=credit+1; }
  i=i+1;
}
// assert work + credit <= n
```

---

## ML-Series: Multi-Loop Templates

Multi-loop programs: Loop 1 computes a quantity; Loop 2 uses or verifies it.
The **inter-loop invariant** is the semantic link between the two loops.

### ML1 · Accumulate-Then-Verify
- **Loop 1**: L1 (prefix_sum_family) — computes `sum = f(n)`
- **Loop 2**: L2 (complement_step) — counts down from `sum`
- **Inter-loop invariant**: Loop 2's limit IS Loop 1's output (`sum`)
- **Shared var**: `sum`

### ML2 · GCD-Then-Multiple
- **Loop 1**: X2 (gcd_compare) — computes gcd(a, b)
- **Loop 2**: N11 (accumulate_family) — verifies `a*b == lcm * gcd`
- **Shared vars**: `a`, `b`, gcd result

### ML3 · Multiply-Then-Check
- **Loop 1**: N10 (russian_multiply) — computes `z = a*b`
- **Loop 2**: N11 (accumulate_family) — recomputes same product via addition
- **Shared vars**: `a`, `b`, final product `z`
- **Inter-loop invariant**: both methods yield same result

### ML4 · Normalize-Then-Process
- **Loop 1**: L6 (snapshot_family) — synchronizes two variables to same value
- **Loop 2**: N11 or L1 (accumulate_family) — processes the synchronized value
- **Shared var**: final synchronized value

### ML5 · SearchRoot-Then-Bound
- **Loop 1**: N8 (int_sqrt_sieve) — finds integer sqrt `r` of `a`
- **Loop 2**: N9 (cauchy_schwarz_triple) — uses `r` as parameter for quadratic accumulation
- **Shared vars**: `r`, `a`

### ML6 · Phase-Split-Then-Merge
- **Loop 1**: L11 (mod_bucket_cascade) — distributes `i` steps across `j` and `k`
- **Loop 2**: L1 (prefix_sum_family) — accumulates from both `j` and `k`
- **Shared vars**: `i`, `j`, `k`

### ML7 · Decompose-Then-Recompose
- **Loop 1**: N5 (qr_division_step) — decomposes `x = y*q + r`
- **Loop 2**: N11 (accumulate_family) — verifies `y*q` by repeated addition
- **Shared vars**: `x`, `y`, `q`, `r`

### ML8 · Refine-Then-Saturate
- **Loop 1**: X3 (fixed_point_root_refinement) — narrows `[lo, hi]` interval
- **Loop 2**: L8 (saturation) — saturates a counter from `lo` toward `hi`
- **Shared vars**: `lo`, `hi`

---

## Input Coverage Audit

| Input Range | Pattern | Template |
|---|---|---|
| linear/1, 2, 172 | affine accumulator | L1 |
| linear/25, 100, 101 | countdown to zero | L2 |
| linear/154 | proportional stride | L3 |
| linear/10, 316 | conservation law | L4 |
| linear/145 | countdown triple | L5 |
| linear/124, 125, 160, 270 | snapshot chase | L6 |
| linear/176 | parity flip-flop | L7 |
| linear/35–37, 50, 55 | saturation guard | L8 |
| linear/75 | sliding window | L9 |
| linear/150 | piecewise multi-rate | L10 |
| linear/300, 316 | triple modular step | L11 |
| linear/101, 201 | monotone increment | L12 |
| linear/260 | binary toggle | L13 |
| linear/212–215 | cache coherence | L14 |
| linear/200 | multi-countdown | L15 |
| linear/3 | min-tracking update | L16 |
| linear/130 | linked countdown | L19 |
| linear/250 | decaying stride | L20 |
| NLA/1 | polynomial finite diff | N1 |
| NLA/15 | triangular sum | N2 |
| NLA/16 | square sum | N3 |
| NLA/17, 18, 19 | higher power sums | N4 |
| NLA/2, 3, 4, 12 | quotient-remainder | N5 |
| NLA/5, 6, 7, 8 | extended euclidean | N6 |
| NLA/10, 11 | geometric series | N7 |
| NLA/20, 36, 43, 44 | integer sqrt sieve | N8 |
| NLA/29, 30 | Cauchy-Schwarz | N9 |
| NLA/14 | Russian peasant mult | N10 |
| NLA/31, 40, 42 | product by addition | N11 |
| NLA/21, 22 | squared invariant | N12 |
| NLA/25 | affine geometric | N13 |
| NLA/50, 51 | complex piecewise | N14 |

**Total templates**: 42 (20 L-series + 14 N-series + 8 X-series with analogs + ML pairing layer)

---

## Verification Commands

```bash
# 1. Every loop has a named template (not "none")
python3 loop_factory.py --count 50 --seed 42 | grep -c "core: none"
# Expected: 0

# 2. Generate multi-loop programs and inspect pairing
python3 loop_factory.py --count 20 --min-loops 2 --max-loops 2 --seed 42

# 3. Trace score check (all programs should score >= 0.40)
python3 -c "
from loop_factory import ProbabilisticLoopFactory, HyperParams, trace_score
import random
hp = HyperParams()
f = ProbabilisticLoopFactory(hp, random.Random(42))
scores = [trace_score(f.sample_program(i)) for i in range(30)]
print(f'min={min(scores):.2f} mean={sum(scores)/len(scores):.2f}')
"

# 4. Coverage check: all 35+ template names appear within 200 samples
python3 loop_factory.py --count 200 --seed 1
```


---

## Uncovered Pattern Backlog (Draft Templates)

Why current coverage is low:
- `src/input/linear` is very large (316 files) while current catalog cites a small representative subset.
- X/ML templates are mostly synthetic/compositional and therefore often have no direct `Sources` lines.
- Several existing `Sources` entries were illustrative and not exhaustive (by design), so union coverage undercounts practical semantic reach.

Current audit snapshot:
- Covered in `linear`: 33 / 316
- Covered in `NLA_lipus`: 31 / 50
- Covered overall in `src/input`: 64 / 366

### Proposed New Template Drafts for Uncovered Inputs

#### U1 · Monotone Branch-Walk with Signed Drift (linear-heavy)
**Target gaps**: broad linear ranges with piecewise `+/-` drift and guard switching.
**Pattern**:
```c
while (i < n) {
  if (x - y < k) { x = x + a1; y = y + b1; }
  else           { x = x + a2; y = y + b2; }
  i = i + 1;
}
```

#### U2 · Multi-Bucket Counter Lattice (linear modular families)
**Target gaps**: modular partition problems beyond current 2-3 bucket variants.
**Pattern**:
```c
while (i < n) {
  if (i % p1 == 0) c1++;
  else if (i % p2 == 0) c2++;
  else if (i % p3 == 0) c3++;
  else c0++;
  i++;
}
```

#### U3 · Coupled Countdown with Regeneration (linear state-machine)
**Target gaps**: countdown loops where one counter periodically resets/reloads another.
**Pattern**:
```c
while (x > 0 || y > 0) {
  if (x > 0) x--;
  else { x = refill; y--; }
}
```

#### U4 · Affine Phase Scheduler (linear multi-phase)
**Target gaps**: inputs with explicit phase variable and per-phase affine updates.
**Pattern**:
```c
while (t < n) {
  if (phase == 0) { a += p; b += q; }
  else            { a += r; b -= s; }
  if (t % m == 0) phase = 1 - phase;
  t++;
}
```

#### U5 · Division-with-Compensation (NLA missing 9/13/23-24/26-28)
**Target gaps**: NLA cases mixing division/quotient update with compensation accumulator.
**Pattern**:
```c
while (x > 0) {
  q = q + x / d;
  c = c + x % d;
  x = x / d;
}
```

#### U6 · Piecewise Power-Accumulate with Guarded Clamp (NLA missing 32-35/37-39)
**Target gaps**: nonlinear accumulators where growth is clamped or redirected by guard.
**Pattern**:
```c
while (i < n) {
  if (z < B) z = z * k + a;
  else       z = z - c;
  s = s + z;
  i++;
}
```

#### U7 · Residual Refinement with Rolling Error (NLA missing 41/46-49)
**Target gaps**: root/refinement-like loops with residual feedback.
**Pattern**:
```c
while (lo + 1 < hi) {
  mid = (lo + hi) / 2;
  err = f(mid);
  if (err <= 0) lo = mid;
  else          hi = mid;
  acc = acc + err;
}
```

### Integration Plan (next implementation pass)
- Add U1-U7 as new cores with `allow(...)` hooks and per-core native expansion styles.
- Attach each U-template to a semantic ID block (prefer `X21+` or fold into existing X/N IDs with aliases).
- Update `Input Coverage Audit` table with concrete `Sources` after first successful batch mapping run.
- Keep assertions Frama-C friendly (linear consequences for inherently exponential/nonlinear behaviors).
