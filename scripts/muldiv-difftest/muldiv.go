package main

import (
	"fmt"
	"math/rand"

	big "github.com/ethereum/go-bigmodexpfix/src/math/big"
)

var imports = []string{"BitsNat", "MulClosed", "DivBasic", "DivClosed"}

func emitMulDiv(r *rand.Rand) {
	sizes := []int{0, 1, 2, 3, 5, 11, 12, 13, 39, 40, 41, 57, 80, 81, 97}
	for _, m := range sizes {
		for _, n := range []int{1, 2, 7, 40, 41, 80} {
			if n > m+40 {
				continue
			}
			x, y := big.FvRandWords(r, m), big.FvRandWords(r, n)
			fmt.Printf("#guard natMul %s %s == %s\n", L(x), L(y), L(big.FvMul(x, y)))
		}
		x := big.FvRandWords(r, m)
		fmt.Printf("#guard natSqr %s == %s\n", L(x), L(big.FvSqr(x)))
		if m > 0 {
			fmt.Printf("#guard basicSqr (List.replicate %d 0) %s == %s\n", 2*m, L(x), L(big.FvBasicSqr(x)))
			y := big.FvRandWords(r, m)
			fmt.Printf("#guard karatsubaC %s %s == %s\n", L(x), L(y), L(big.FvKaratsuba(x, y)))
			fmt.Printf("#guard karatsubaSqrC %s == %s\n", L(x), L(big.FvKaratsubaSqr(x)))
		}
	}
	// divBasic: v normalised (n >= 2), u arbitrary with len(u) >= n, len(q) = m+1 (zeros) or len(q) = m with top digit 0
	for t := 0; t < 120; t++ {
		n := 2 + r.Intn(12)
		m := r.Intn(10)
		v := topSet(r, n)
		if r.Intn(4) == 0 { // divisor with many ~0 / 0 limbs below a top word near 2^63
			for i := 0; i < n-1; i++ { v[i] = ^uint64(0) * uint64(r.Intn(2)) }
			v[n-1] = 1<<63 + uint64(r.Intn(3))
		}
		u := big.FvRandWords(r, m+n)
		qlen := m + 1
		if r.Intn(3) == 0 { // divLarge shape: top word of u below v's top word -> len(q) = m
			u[m+n-1] = uint64(r.Int63n(int64(v[n-1] >> 1)))
			qlen = m
		}
		if r.Intn(5) == 0 { // u = v * k (exact)
			for i := 0; i < m+n; i++ { u[i] = 0 }
			copy(u[m:], v)
			if qlen == m { u[m+n-1] = 0 }
		}
		q := make([]uint64, qlen)
		q2, u2 := big.FvDivBasic(q, u, v)
		fmt.Printf("#guard divBasic %s %s %s == (%s, %s)\n", L(q), L(u), L(v), L(q2), L(u2))
	}
	// divRecursive in the divLarge shape: n >= 40, len(q) = len(u) - n, top limb of u < 2^63
	for t := 0; t < 30; t++ {
		n := 40 + r.Intn(60)
		m := r.Intn(70)
		v := topSet(r, n)
		u := big.FvRandWords(r, m+n)
		u[m+n-1] >>= 1 + uint(r.Intn(63))
		q := make([]uint64, m)
		q2, u2 := big.FvDivRecursive(q, u, v)
		fmt.Printf("#guard divRecursiveC %s %s %s == (%s, %s)\n", L(q), L(u), L(v), L(q2), L(u2))
	}
	// nat.div on normalised operands, all size regimes (divW, u < v, divBasic, divRecursive)
	for t := 0; t < 80; t++ {
		n := 1 + r.Intn(100)
		m := r.Intn(130)
		v := big.FvRandWords(r, n)
		v[n-1] |= uint64(1) << uint(r.Intn(64))
		u := big.FvRandWords(r, m)
		for len(u) > 0 && u[len(u)-1] == 0 {
			u = u[:len(u)-1]
		}
		q2, r2 := big.FvDiv(u, v)
		fmt.Printf("#guard natDivC %s %s == (%s, %s)\n", L(u), L(v), L(q2), L(r2))
	}
}
