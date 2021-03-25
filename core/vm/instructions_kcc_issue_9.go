package vm

import (
	"github.com/ethereum/go-ethereum/common"
)

// Update: We found another similiar malicious transaction at block #2539630.
//
//	And this transaction was processed by a KCC client of v1.0.5.
//
// On KCC mainnet, there was a malicious transaction at block #2509228,
// which tried to split KCC nodes into different chains.
// This transaction exploited CVE-2021-39137.
//
// Luckily, KCC did not split, and KCC has fixed this issue since v1.0.4.
// But this caused another problem in synchronization:
// With KCC v1.0.4 or v1.0.5, it is not able to synchronize in full mode from a block earlier than block #2509228.
// (related github issue: https://github.com/kcc-community/kcc/issues/9):
//
// The malicious TX (https://scan.kcc.io/tx/0xe42c11a8a31f3c0a990a8264b23bf4e936b9d97f3242cfbc21e63b2b0abd09f0) created
// a new contract. Due to CVE-2021-39137, the contract runtime codes created in KCC v1.0.3 and in KCC v1.0.4 are
// not the same, this will result in different merkle roots, and eventually halt the synchronization.
//
// ps: we have added a hive integration test case on this issue.
//
// References:
// 1. KCC #9 : https://github.com/kcc-community/kcc/issues/9
// 2. Postmortem report from go-ethereum: https://github.com/ethereum/go-ethereum/blob/master/docs/postmortems/2021-08-22-split-postmortem.md
// 3. The malicious TX: https://scan.kcc.io/tx/0xe42c11a8a31f3c0a990a8264b23bf4e936b9d97f3242cfbc21e63b2b0abd09f0
func opVulnerableStaticCall(pc *uint64, interpreter *EVMInterpreter, callContext *ScopeContext) ([]byte, error) {
	// Pop gas. The actual gas is in interpreter.evm.callGasTemp.
	stack := callContext.Stack
	// We use it as a temporary value
	temp := stack.pop()
	gas := interpreter.evm.callGasTemp
	// Pop other call parameters.
	addr, inOffset, inSize, retOffset, retSize := stack.pop(), stack.pop(), stack.pop(), stack.pop(), stack.pop()
	toAddr := common.Address(addr.Bytes20())
	// Get arguments from the memory.
	args := callContext.Memory.GetPtr(int64(inOffset.Uint64()), int64(inSize.Uint64()))

	ret, returnGas, err := interpreter.evm.StaticCall(callContext.Contract, toAddr, args, gas)
	if err != nil {
		temp.Clear()
	} else {
		temp.SetOne()
	}
	stack.push(&temp)
	if err == nil || err == ErrExecutionReverted {
		// TX 0xe42c11a8a31f3c0a990a8264b23bf4e936b9d97f3242cfbc21e63b2b0abd09f0 would result
		// in a differenct contract runtime code with the following commented line.
		// ret = common.CopyBytes(ret)
		callContext.Memory.Set(retOffset.Uint64(), retSize.Uint64(), ret)
	}
	callContext.Contract.Gas += returnGas

	return ret, nil
}

func UseVulnerableCalls(jt *JumpTable) {
	jt[STATICCALL].execute = opVulnerableStaticCall
}
