package main

import (
	"fmt"
	"math/rand"

	big "github.com/ethereum/go-bigmodexpfix/src/math/big"
)

var imports = []string{"BitsNat", "MulClosed"}

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
}
