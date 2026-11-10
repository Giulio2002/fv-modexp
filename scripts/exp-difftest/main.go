package main

import (
	"fmt"
	"math/rand"

	big "github.com/ethereum/go-bigmodexpfix/src/math/big"
)

func s(z big.FvNat) string { return big.FvToInt(z).String() }

func nz(r *rand.Rand, w int) big.FvNat {
	for {
		z := big.FvRand(r, w)
		if len(z) > 0 {
			return z
		}
	}
}
func odd(r *rand.Rand, w int) big.FvNat {
	for {
		z := nz(r, w)
		if z[0]&1 == 1 {
			return z
		}
	}
}

func main() {
	r := rand.New(rand.NewSource(12345))
	fmt.Println("import FvModexp.Proofs.Common.ExpNN\nopen FvModexp.Exp")
	for i := 0; i < 40; i++ {
		n := 1 + r.Intn(3)
		var m big.FvNat
		for {
			m = odd(r, n)
			if len(m) == n {
				break
			}
		}
		x := big.FvRand(r, n)
		y := big.FvRand(r, n)
		k := big.FvK0(uint64(m[0]))
		fmt.Printf("#guard montK0 (%s %% B) == %d\n", s(m), k)
		fmt.Printf("#guard montgomery %d %s %s %s %d == %s\n", n, s(x), s(y), s(m), k, s(big.FvMontgomery(x, y, m, k, n)))
	}
	ns := []uint{1, 2, 5, 31, 63, 64, 65, 100, 127, 128, 129, 192, 200, 256, 257, 300, 513}
	for i := 0; i < 60; i++ {
		x := odd(r, 1+r.Intn(5))
		n := ns[r.Intn(len(ns))]
		fmt.Printf("#guard modularInverseModPowerOfTwo %s %d == %s\n", s(x), n, s(big.FvModInvP2(x, n)))
		a := big.FvRand(r, 1+r.Intn(4))
		b := big.FvRand(r, 1+r.Intn(4))
		fmt.Printf("#guard subMod2N %s %s %d == %s\n", s(a), s(b), n, s(big.FvSubMod2N(a, b, n)))
	}
	for i := 0; i < 40; i++ {
		m := odd(r, 1+r.Intn(2))
		x := nz(r, 1+r.Intn(3))
		y := nz(r, 1+r.Intn(3))
		for _, w := range []int{2, 4} {
			fmt.Printf("#guard expNNOddMont %d %s %s %s == %s\n", w, s(x), s(y), s(m), s(big.FvOdd(x, y, m, w)))
		}
	}
	ls := []uint{1, 2, 3, 5, 47, 48, 63, 64, 65, 66, 130, 200}
	for i := 0; i < 60; i++ {
		x := nz(r, 1+r.Intn(3))
		if i%3 == 0 {
			x[0] &^= 7
			x = big.FvFromWords(func() []uint64 { o := make([]uint64, len(x)); for j := range x { o[j] = uint64(x[j]) }; return o }())
			if len(x) == 0 {
				x = big.FvFromWords([]uint64{8})
			}
		}
		y := nz(r, 1+r.Intn(2))
		if i%4 == 0 {
			y = big.FvFromWords([]uint64{uint64(1 + r.Intn(70))})
		}
		l := ls[r.Intn(len(ls))]
		fmt.Printf("#guard expNNPowerOfTwo 2 %s %s %d == %s\n", s(x), s(y), l, s(big.FvPow2(x, y, l)))
	}
	for i := 0; i < 30; i++ {
		x := nz(r, 1+r.Intn(2))
		y := nz(r, 1+r.Intn(2))
		if len(y) == 1 && y[0] < 2 {
			continue
		}
		m := nz(r, 1+r.Intn(2))
		fmt.Printf("#guard expNNSlow %s %s %s == %s\n", s(x), s(y), s(m), s(big.FvSlow(x, y, m)))
	}
	for i := 0; i < 5; i++ {
		x := big.FvFromWords([]uint64{uint64(2 + r.Intn(100))})
		y := big.FvFromWords([]uint64{uint64(2 + r.Intn(30))})
		fmt.Printf("#guard expNNSlow %s %s 0 == %s\n", s(x), s(y), s(big.FvSlow(x, y, nil)))
	}
	for i := 0; i < 40; i++ {
		m := nz(r, 1+r.Intn(3))
		m[0] &^= 1
		if len(m) == 1 && m[0] == 0 { continue }
		if m[0] == 0 && len(m) > 1 { m[0] = 2 }
		mm := big.FvFromWords(func() []uint64 { o := make([]uint64, len(m)); for j := range m { o[j] = uint64(m[j]) }; return o }())
		if _, ok := func() (int, bool) { c := 0; for _, w := range mm { for v := w; v != 0; v &= v - 1 { c++ } }; return c, c == 1 }(); ok { continue }
		x := nz(r, 1+r.Intn(3))
		y := nz(r, 1+r.Intn(2))
		if len(y) == 1 && y[0] < 2 { continue }
		fmt.Printf("#guard expNNEven (fun x y m => expNN 1 x y m false) %s %s %s == %s\n", s(x), s(y), s(mm), s(big.FvEven(x, y, mm)))
		fmt.Printf("#guard expNN 2 %s %s %s false == %s\n", s(x), s(y), s(mm), s(big.FvExpNN(x, y, mm)))
	}
	for i := 0; i < 60; i++ {
		x := big.FvRand(r, r.Intn(3))
		y := big.FvRand(r, r.Intn(3))
		m := big.FvRand(r, 1+r.Intn(3))
		if len(m) == 0 { continue }
		if i%5 == 0 { y = big.FvFromWords([]uint64{uint64(r.Intn(40))}) }
		if i%7 == 0 { m = big.FvFromWords([]uint64{1}) }
		fmt.Printf("#guard expNN 2 %s %s %s false == %s\n", s(x), s(y), s(m), s(big.FvExpNN(x, y, m)))
	}
}
