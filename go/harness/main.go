// Command harness links geth v1.17.10's MODEXP precompile (the Osaka precompile set, address 0x05)
// so that janus can extract (*bigModExp).Run and (*bigModExp).RequiredGas from the executable.
package main

import (
	"os"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/vm"
)

func main() {
	p := vm.PrecompiledContractsOsaka[common.BytesToAddress([]byte{0x05})]
	in, _ := os.ReadFile(os.Args[1])
	gas := p.RequiredGas(in)
	out, err := p.Run(in)
	os.Stdout.WriteString(common.Bytes2Hex(out))
	if err != nil || gas == 0 {
		os.Exit(1)
	}
}
