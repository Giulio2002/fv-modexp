// Differential test driver: prints Lean `#guard` lines comparing the mathdiv Nat-level models with the real
// go-bigmodexpfix f9e208c548ab functions (exported by fvexport.go). Fixed seed.
package main

import (
	"fmt"
	"math/rand"
	"strings"

	big "github.com/ethereum/go-bigmodexpfix/src/math/big"
)

func L(w []uint64) string {
	s := make([]string, len(w))
	for i, v := range w {
		s[i] = fmt.Sprint(v)
	}
	return "[" + strings.Join(s, ", ") + "]"
}
func LB(b []byte) string {
	s := make([]string, len(b))
	for i, v := range b {
		s[i] = fmt.Sprint(v)
	}
	return "[" + strings.Join(s, ", ") + "]"
}

// topSet: random words with the top bit of the last limb set (normalised divisor).
func topSet(r *rand.Rand, n int) []uint64 {
	v := big.FvRandWords(r, n)
	v[n-1] |= 1 << 63
	return v
}

func main() {
	r := rand.New(rand.NewSource(20261110))
	for _, m := range imports { fmt.Println("import FvModexp.Proofs.Common." + m) }
	fmt.Println("open FvModexp.Mdl")
	// bytes / setBytes / bitLen
	for i := 0; i < 40; i++ {
		n := r.Intn(40)
		b := make([]byte, n)
		for j := range b {
			b[j] = byte(r.Intn(256))
			if r.Intn(3) == 0 {
				b[j] = 0
			}
		}
		z := big.FvSetBytes(b)
		fmt.Printf("#guard natSetBytes %s == %s\n", LB(b), L(z))
		fmt.Printf("#guard intBytes %s == %s\n", L(z), LB(big.FvBytes(z)))
		fmt.Printf("#guard natBitLen %s == %d\n", L(z), big.FvBitLen(z))
	}
	emitMulDiv(r)
}
