package native

import (
	"encoding/json"
	"errors"
	"fmt"
	"math/big"
	"strings"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/vm"
	"github.com/ethereum/go-ethereum/eth/tracers"
)

func init() {
	register("oeTracer", newOeTracer)
}

const (
	CALL         = "call"
	CALLCODE     = "callcode"
	DELEGATECALL = "delegatecall"
	STATICCALL   = "staticcall"
	CREATE       = "create"
	SUICIDE      = "suicide"
)

// ParityTrace trace (Parity/OpenEtherum) See: https://openethereum.github.io/JSONRPC-trace-module
type ParityTrace struct {
	Action              interface{}  `json:"action"` // Can be either CallTraceAction or CreateTraceAction
	BlockHash           *common.Hash `json:"blockHash,omitempty"`
	BlockNumber         *uint64      `json:"blockNumber,omitempty"`
	Error               string       `json:"error,omitempty"`
	Result              interface{}  `json:"result"`
	Subtraces           int          `json:"subtraces"`
	TraceAddress        []int        `json:"traceAddress"`
	TransactionHash     *common.Hash `json:"transactionHash,omitempty"`
	TransactionPosition *uint64      `json:"transactionPosition,omitempty"`
	Type                string       `json:"type"`
}

type ParityTraces []ParityTrace

// TraceAction is the parity formatted action of a trace
type TraceAction struct {
	Author         string         `json:"author,omitempty"`
	RewardType     string         `json:"rewardType,omitempty"`
	SelfDestructed string         `json:"address,omitempty"`
	Balance        string         `json:"balance,omitempty"`
	CallType       string         `json:"callType,omitempty"`
	From           common.Address `json:"from"`
	Gas            hexutil.Big    `json:"gas"`
	Init           hexutil.Bytes  `json:"init,omitempty"`
	Input          hexutil.Bytes  `json:"input,omitempty"`
	RefundAddress  string         `json:"refundAddress,omitempty"`
	To             string         `json:"to,omitempty"`
	Value          string         `json:"value,omitempty"`
}

// CallTraceAction is the parity formatted action of a call trace
type CallTraceAction struct {
	From     common.Address `json:"from"`
	CallType string         `json:"callType"`
	Gas      hexutil.Big    `json:"gas"`
	Input    hexutil.Bytes  `json:"input"`
	To       common.Address `json:"to"`
	Value    hexutil.Big    `json:"value"`
}

// CreateTraceAction is the parity formatted action of a create trace
type CreateTraceAction struct {
	From  common.Address `json:"from"`
	Gas   hexutil.Big    `json:"gas"`
	Init  hexutil.Bytes  `json:"init"`
	Value hexutil.Big    `json:"value"`
}

// SuicideTraceAction is the parity formatted action of a create trace
type SuicideTraceAction struct {
	Address       common.Address `json:"address"`
	RefundAddress common.Address `json:"refundAddress"`
	Balance       hexutil.Big    `json:"balance"`
}

// RewardTraceAction is the parity formatted action of a reward trace
type RewardTraceAction struct {
	Author     common.Address `json:"author"`
	RewardType string         `json:"rewardType"`
	Value      hexutil.Big    `json:"value,omitempty"`
}

type CreateTraceResult struct {
	Address *common.Address `json:"address,omitempty"`
	Code    hexutil.Bytes   `json:"code"`
	GasUsed *hexutil.Big    `json:"gasUsed"`
}

type TraceResult struct {
	GasUsed *hexutil.Big  `json:"gasUsed"`
	Output  hexutil.Bytes `json:"output"`
}

// TraceCallResult is the result of trace
type TraceCallResult struct {
	Output    hexutil.Bytes                        `json:"output"`
	StateDiff map[common.Address]*StateDiffAccount `json:"stateDiff"`
	Trace     []*ParityTrace                       `json:"trace"`
	VmTrace   *VmTrace                             `json:"vmTrace"`
}

// StateDiffAccount is the state difference. Provides information detailing all altered portions of the Ethereum state made due to the execution of the transaction.
type StateDiffAccount struct {
	Balance interface{}                            `json:"balance"` // Can be either string "=" or mapping "*" => {"from": "hex", "to": "hex"}
	Code    interface{}                            `json:"code"`
	Nonce   interface{}                            `json:"nonce"`
	Storage map[common.Hash]map[string]interface{} `json:"storage"`
}

type StateDiffBalance struct {
	From *hexutil.Big `json:"from"`
	To   *hexutil.Big `json:"to"`
}

type StateDiffCode struct {
	From hexutil.Bytes `json:"from"`
	To   hexutil.Bytes `json:"to"`
}

type StateDiffNonce struct {
	From hexutil.Uint64 `json:"from"`
	To   hexutil.Uint64 `json:"to"`
}

type StateDiffStorage struct {
	From common.Hash `json:"from"`
	To   common.Hash `json:"to"`
}

// VmTrace is the virtual machine execution trace. Provides a full trace of the VM’s state throughout the execution of the transaction, including for any subcalls.
type VmTrace struct {
	Code hexutil.Bytes `json:"code"`
	Ops  []*VmTraceOp  `json:"ops"`
}

// VmTraceOp is one element of the vmTrace ops trace
type VmTraceOp struct {
	Cost int        `json:"cost"`
	Ex   *VmTraceEx `json:"ex"`
	Pc   int        `json:"pc"`
	Sub  *VmTrace   `json:"sub"`
	Op   string     `json:"op,omitempty"`
	Idx  string     `json:"idx,omitempty"`
}

type VmTraceEx struct {
	Mem   *VmTraceMem   `json:"mem"`
	Push  []string      `json:"push"`
	Store *VmTraceStore `json:"store"`
	Used  int           `json:"used"`
}

type VmTraceMem struct {
	Data string `json:"data"`
	Off  int    `json:"off"`
}

type VmTraceStore struct {
	Key string `json:"key"`
	Val string `json:"val"`
}

// OpenEthereum-style tracer
type OeTracer struct {
	result       *TraceCallResult
	traceAddr    []int
	traceStack   []*ParityTrace
	lastVmOp     *VmTraceOp
	lastOp       vm.OpCode
	lastMemOff   uint64
	lastMemLen   uint64
	memOffStack  []uint64
	memLenStack  []uint64
	lastOffStack *VmTraceOp
	vmOpStack    []*VmTraceOp
	idx          []string
}

type oeTracerConfig struct {
	Trace     bool `json:"trace"`     // If true, will trace the execution of the transaction
	StateDiff bool `json:"stateDiff"` // If true, will trace the state difference
	VmTrace   bool `json:"vmTrace"`   // If true, will trace the virtual machine execution
}

// newOeTracer returns a new oe tracer.
func newOeTracer(ctx *tracers.Context, cfg json.RawMessage) (tracers.Tracer, error) {
	var config oeTracerConfig
	if cfg != nil {
		if err := json.Unmarshal(cfg, &config); err != nil {
			return nil, err
		}
	}

	return NewOeTracer(config.Trace, config.StateDiff, config.VmTrace), nil
}

func NewOeTracer(traceTypeTrace, traceTypeStateDiff, traceTypeVmTrace bool) tracers.Tracer {
	var oeTracer OeTracer
	oeTracer.result = &TraceCallResult{}
	if traceTypeTrace {
		oeTracer.result.Trace = make([]*ParityTrace, 0)
	}
	if traceTypeStateDiff {
		oeTracer.result.StateDiff = make(map[common.Address]*StateDiffAccount)
	}
	if traceTypeVmTrace {
		oeTracer.result.VmTrace = &VmTrace{
			Ops: make([]*VmTraceOp, 0),
		}
	}
	return &oeTracer
}

func (ot *OeTracer) CaptureTxStart(uint64) {}

func (ot *OeTracer) CaptureTxEnd(uint64) {}

func (ot *OeTracer) captureStartOrEnter(deep bool, typ vm.OpCode, from common.Address, to common.Address, create bool, input []byte, gas uint64, value *big.Int) {
	if ot.result.VmTrace != nil {
		var vmTrace *VmTrace
		if deep {
			var vmT *VmTrace
			if len(ot.vmOpStack) > 0 {
				vmT = ot.vmOpStack[len(ot.vmOpStack)-1].Sub
			} else {
				vmT = ot.result.VmTrace
			}
			ot.idx = append(ot.idx, fmt.Sprintf("%d-", len(vmT.Ops)-1))
		}
		if ot.lastVmOp != nil {
			vmTrace = &VmTrace{Ops: []*VmTraceOp{}}
			ot.lastVmOp.Sub = vmTrace
			ot.vmOpStack = append(ot.vmOpStack, ot.lastVmOp)
		} else {
			vmTrace = ot.result.VmTrace
		}
		if create {
			vmTrace.Code = common.CopyBytes(input)
			if ot.lastVmOp != nil {
				ot.lastVmOp.Cost += int(gas)
			}
		}
	}
	trace := &ParityTrace{}
	if create {
		trResult := &CreateTraceResult{}
		trace.Type = CREATE
		trResult.Address = new(common.Address)
		copy(trResult.Address[:], to.Bytes())
		trace.Result = trResult
	} else {
		trace.Result = &TraceResult{}
		trace.Type = CALL
	}
	if deep {
		topTrace := ot.traceStack[len(ot.traceStack)-1]
		traceIdx := topTrace.Subtraces
		ot.traceAddr = append(ot.traceAddr, traceIdx)
		topTrace.Subtraces++
		if typ == vm.DELEGATECALL {
			switch action := topTrace.Action.(type) {
			case *CreateTraceAction:
				value = action.Value.ToInt()
			case *CallTraceAction:
				value = action.Value.ToInt()
			}
		}
		if typ == vm.STATICCALL {
			value = big.NewInt(0)
		}
	}
	trace.TraceAddress = make([]int, len(ot.traceAddr))
	copy(trace.TraceAddress, ot.traceAddr)
	if create {
		action := CreateTraceAction{}
		action.From = from
		action.Gas.ToInt().SetUint64(gas)
		action.Init = common.CopyBytes(input)
		action.Value.ToInt().Set(value)
		trace.Action = &action
	} else if typ == vm.SELFDESTRUCT {
		trace.Type = SUICIDE
		trace.Result = nil
		action := &SuicideTraceAction{}
		action.Address = from
		action.RefundAddress = to
		action.Balance.ToInt().Set(value)
		trace.Action = action
	} else {
		action := CallTraceAction{}
		switch typ {
		case vm.CALL:
			action.CallType = CALL
		case vm.CALLCODE:
			action.CallType = CALLCODE
		case vm.DELEGATECALL:
			action.CallType = DELEGATECALL
		case vm.STATICCALL:
			action.CallType = STATICCALL
		}
		action.From = from
		action.To = to
		action.Gas.ToInt().SetUint64(gas)
		action.Input = common.CopyBytes(input)
		action.Value.ToInt().Set(value)
		trace.Action = &action
	}
	ot.result.Trace = append(ot.result.Trace, trace)
	ot.traceStack = append(ot.traceStack, trace)
}

func (ot *OeTracer) CaptureStart(env *vm.EVM, from common.Address, to common.Address, create bool, input []byte, gas uint64, value *big.Int) {
	ot.captureStartOrEnter(false, vm.CALL, from, to, create, input, gas, value)
}

func (ot *OeTracer) CaptureEnter(typ vm.OpCode, from common.Address, to common.Address, input []byte, gas uint64, value *big.Int) {
	ot.captureStartOrEnter(true, typ, from, to, typ == vm.CREATE || typ == vm.CREATE2, input, gas, value)
}

func (ot *OeTracer) captureEndOrExit(deep bool, output []byte, usedGas uint64, err error) {
	if ot.result.VmTrace != nil {
		if len(ot.vmOpStack) > 0 {
			ot.lastOffStack = ot.vmOpStack[len(ot.vmOpStack)-1]
			ot.vmOpStack = ot.vmOpStack[:len(ot.vmOpStack)-1]
		}
		if deep {
			ot.idx = ot.idx[:len(ot.idx)-1]
		}
		if deep {
			ot.lastMemOff = ot.memOffStack[len(ot.memOffStack)-1]
			ot.memOffStack = ot.memOffStack[:len(ot.memOffStack)-1]
			ot.lastMemLen = ot.memLenStack[len(ot.memLenStack)-1]
			ot.memLenStack = ot.memLenStack[:len(ot.memLenStack)-1]
		}
	}
	if !deep {
		ot.result.Output = common.CopyBytes(output)
	}
	ignoreError := false
	topTrace := ot.traceStack[len(ot.traceStack)-1]
	if err != nil && !ignoreError {
		if err == vm.ErrExecutionReverted {
			topTrace.Error = "Reverted"
			switch topTrace.Type {
			case CALL:
				topTrace.Result.(*TraceResult).GasUsed = new(hexutil.Big)
				topTrace.Result.(*TraceResult).GasUsed.ToInt().SetUint64(usedGas)
				topTrace.Result.(*TraceResult).Output = common.CopyBytes(output)
			case CREATE:
				topTrace.Result.(*CreateTraceResult).GasUsed = new(hexutil.Big)
				topTrace.Result.(*CreateTraceResult).GasUsed.ToInt().SetUint64(usedGas)
				topTrace.Result.(*CreateTraceResult).Code = common.CopyBytes(output)
			}
		} else {
			topTrace.Result = nil
			topTrace.Error = err.Error()
		}
	} else {
		if len(output) > 0 {
			switch topTrace.Type {
			case CALL:
				topTrace.Result.(*TraceResult).Output = common.CopyBytes(output)
			case CREATE:
				topTrace.Result.(*CreateTraceResult).Code = common.CopyBytes(output)
			}
		}
		switch topTrace.Type {
		case CALL:
			topTrace.Result.(*TraceResult).GasUsed = new(hexutil.Big)
			topTrace.Result.(*TraceResult).GasUsed.ToInt().SetUint64(usedGas)
		case CREATE:
			topTrace.Result.(*CreateTraceResult).GasUsed = new(hexutil.Big)
			topTrace.Result.(*CreateTraceResult).GasUsed.ToInt().SetUint64(usedGas)
		}
	}
	ot.traceStack = ot.traceStack[:len(ot.traceStack)-1]
	if deep {
		ot.traceAddr = ot.traceAddr[:len(ot.traceAddr)-1]
	}
}

func (ot *OeTracer) CaptureEnd(output []byte, usedGas uint64, _ time.Duration, err error) {
	ot.captureEndOrExit(false /* deep */, output, usedGas, err)
}

func (ot *OeTracer) CaptureExit(output []byte, usedGas uint64, err error) {
	ot.captureEndOrExit(true /* deep */, output, usedGas, err)
}

func (ot *OeTracer) CaptureState(pc uint64, op vm.OpCode, gas, cost uint64, scope *vm.ScopeContext, rData []byte, opDepth int, err error) {
	memory := scope.Memory
	st := scope.Stack

	if ot.result.VmTrace != nil {
		var vmTrace *VmTrace
		if len(ot.vmOpStack) > 0 {
			vmTrace = ot.vmOpStack[len(ot.vmOpStack)-1].Sub
		} else {
			vmTrace = ot.result.VmTrace
		}
		if ot.lastVmOp != nil && ot.lastVmOp.Ex != nil {
			var showStack int
			switch {
			case ot.lastOp >= vm.PUSH1 && ot.lastOp <= vm.PUSH32:
				showStack = 1
			case ot.lastOp >= vm.SWAP1 && ot.lastOp <= vm.SWAP16:
				showStack = int(ot.lastOp-vm.SWAP1) + 2
			case ot.lastOp >= vm.DUP1 && ot.lastOp <= vm.DUP16:
				showStack = int(ot.lastOp-vm.DUP1) + 2
			}
			switch ot.lastOp {
			case vm.CALLDATALOAD, vm.SLOAD, vm.MLOAD, vm.CALLDATASIZE, vm.LT, vm.GT, vm.DIV, vm.SDIV, vm.SAR, vm.AND, vm.EQ, vm.CALLVALUE, vm.ISZERO,
				vm.ADD, vm.EXP, vm.CALLER, vm.KECCAK256, vm.SUB, vm.ADDRESS, vm.GAS, vm.MUL, vm.RETURNDATASIZE, vm.NOT, vm.SHR, vm.SHL,
				vm.EXTCODESIZE, vm.SLT, vm.OR, vm.NUMBER, vm.PC, vm.TIMESTAMP, vm.BALANCE, vm.SELFBALANCE, vm.MULMOD, vm.ADDMOD, vm.BASEFEE,
				vm.BLOCKHASH, vm.BYTE, vm.XOR, vm.ORIGIN, vm.CODESIZE, vm.MOD, vm.SIGNEXTEND, vm.GASLIMIT, vm.DIFFICULTY, vm.SGT, vm.GASPRICE,
				vm.MSIZE, vm.EXTCODEHASH, vm.SMOD, vm.CHAINID, vm.COINBASE:
				showStack = 1
			}
			for i := showStack - 1; i >= 0; i-- {
				if st.Len() > i {
					ot.lastVmOp.Ex.Push = append(ot.lastVmOp.Ex.Push, st.Back(i).String())
				}
			}
			var setMem bool
			switch ot.lastOp {
			case vm.MSTORE, vm.MSTORE8, vm.MLOAD, vm.RETURNDATACOPY, vm.CALLDATACOPY, vm.CODECOPY:
				setMem = true
			}
			if setMem && ot.lastMemLen > 0 {
				cpy := memory.GetCopy(int64(ot.lastMemOff), int64(ot.lastMemLen))
				if len(cpy) == 0 {
					cpy = make([]byte, ot.lastMemLen)
				}
				ot.lastVmOp.Ex.Mem = &VmTraceMem{Data: fmt.Sprintf("0x%0x", cpy), Off: int(ot.lastMemOff)}
			}
		}
		if ot.lastOffStack != nil {
			ot.lastOffStack.Ex.Used = int(gas)
			if st.Len() > 0 {
				ot.lastOffStack.Ex.Push = []string{st.Back(0).String()}
			} else {
				ot.lastOffStack.Ex.Push = []string{}
			}
			if ot.lastMemLen > 0 && memory != nil {
				cpy := memory.GetCopy(int64(ot.lastMemOff), int64(ot.lastMemLen))
				if len(cpy) == 0 {
					cpy = make([]byte, ot.lastMemLen)
				}
				ot.lastOffStack.Ex.Mem = &VmTraceMem{Data: fmt.Sprintf("0x%0x", cpy), Off: int(ot.lastMemOff)}
			}
			ot.lastOffStack = nil
		}
		if ot.lastOp == vm.STOP && op == vm.STOP && len(ot.vmOpStack) == 0 {
			return
		}
		ot.lastVmOp = &VmTraceOp{Ex: &VmTraceEx{}}
		vmTrace.Ops = append(vmTrace.Ops, ot.lastVmOp)
		var sb strings.Builder
		sb.Grow(len(ot.idx))
		for _, idx := range ot.idx {
			sb.WriteString(idx)
		}
		ot.lastVmOp.Idx = fmt.Sprintf("%s%d", sb.String(), len(vmTrace.Ops)-1)
		ot.lastOp = op
		ot.lastVmOp.Cost = int(cost)
		ot.lastVmOp.Pc = int(pc)
		ot.lastVmOp.Ex.Push = []string{}
		ot.lastVmOp.Ex.Used = int(gas) - int(cost)
		ot.lastVmOp.Op = op.String()
		switch op {
		case vm.MSTORE, vm.MLOAD:
			if st.Len() > 0 {
				ot.lastMemOff = st.Back(0).Uint64()
				ot.lastMemLen = 32
			}
		case vm.MSTORE8:
			if st.Len() > 0 {
				ot.lastMemOff = st.Back(0).Uint64()
				ot.lastMemLen = 1
			}
		case vm.RETURNDATACOPY, vm.CALLDATACOPY, vm.CODECOPY:
			if st.Len() > 2 {
				ot.lastMemOff = st.Back(0).Uint64()
				ot.lastMemLen = st.Back(2).Uint64()
			}
		case vm.STATICCALL, vm.DELEGATECALL:
			if st.Len() > 5 {
				ot.memOffStack = append(ot.memOffStack, st.Back(4).Uint64())
				ot.memLenStack = append(ot.memLenStack, st.Back(5).Uint64())
			}
		case vm.CALL, vm.CALLCODE:
			if st.Len() > 6 {
				ot.memOffStack = append(ot.memOffStack, st.Back(5).Uint64())
				ot.memLenStack = append(ot.memLenStack, st.Back(6).Uint64())
			}
		case vm.CREATE, vm.CREATE2, vm.SELFDESTRUCT:
			// Effectively disable memory output
			ot.memOffStack = append(ot.memOffStack, 0)
			ot.memLenStack = append(ot.memLenStack, 0)
		case vm.SSTORE:
			if st.Len() > 1 {
				ot.lastVmOp.Ex.Store = &VmTraceStore{Key: st.Back(0).String(), Val: st.Back(1).String()}
			}
		}
		if ot.lastVmOp.Ex.Used < 0 {
			ot.lastVmOp.Ex = nil
		}
	}
}

func (ot *OeTracer) CaptureFault(pc uint64, op vm.OpCode, gas, cost uint64, scope *vm.ScopeContext, opDepth int, err error) {
}

func (ot *OeTracer) GetResult() (json.RawMessage, error) {
	if ot.result == nil {
		return nil, errors.New("no result")
	}
	return json.Marshal(ot.result.Trace)
}

func (t *OeTracer) Stop(err error) {
}
