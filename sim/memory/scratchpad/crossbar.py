from collections import deque
from dataclasses import dataclass
from typing import List, Optional, Tuple
import math, random

def _is_pow2(n: int) -> bool:
    return n > 0 and (n & (n-1)) == 0

@dataclass
class Switch2x2:
    in0: int; in1: int; out0: int; out1: int
    def route(self, inputs: List[Optional[object]], outputs: List[Optional[object]], sel: int):
        if sel == 0:
            outputs[self.out0] = inputs[self.in0]
            outputs[self.out1] = inputs[self.in1]
        else:
            outputs[self.out0] = inputs[self.in1]
            outputs[self.out1] = inputs[self.in0]

class Stage:
    def __init__(self, N: int):
        self.switches: List[Switch2x2] = []
        self.N = N
    def add_switch(self, sw: Switch2x2):
        self.switches.append(sw)
    def eval(self, inputs: List[Optional[object]], controls: List[int]) -> List[Optional[object]]:
        out = [None]*self.N
        for sw, sel in zip(self.switches, controls):
            sw.route(inputs, out, sel)
        return out

class BenesCBGParity:
    """Deterministic Waksman control-bit generator using a parity-constraint solver (no backtracking)."""
    def __init__(self, N: int):
        if not _is_pow2(N):
            raise ValueError("N must be power of two")
        self.N = N
        self.m = int(math.log2(N))
        self.S = 2*self.m - 1
        self.stages: List[Stage] = [Stage(N) for _ in range(self.S)]
        self._build(0, N, 0, self.S-1)

    def _build(self, base: int, N: int, sf: int, sl: int):
        if N == 1: return
        if N == 2:
            self.stages[sf].add_switch(Switch2x2(base, base+1, base, base+1))
            return
        for i in range(N//2):
            a = base + 2*i
            b = a + 1
            out_top = base + i
            out_bot = base + N//2 + i
            self.stages[sf].add_switch(Switch2x2(a,b,out_top,out_bot))
        self._build(base, N//2, sf+1, sl-1)
        self._build(base+N//2, N//2, sf+1, sl-1)
        for j in range(N//2):
            top_in = base + j
            bot_in = base + N//2 + j
            out0 = base + 2*j
            out1 = base + 2*j + 1
            self.stages[sl].add_switch(Switch2x2(top_in, bot_in, out0, out1))

    # --- Parity-graph solver for T and B ---
    def _assign_TB(self, P: List[int]) -> Tuple[List[int], List[int]]:
        N = len(P)
        V = 2*N  # nodes: 0..N-1 = T[*], N..2N-1 = B[*]
        adj = [[] for _ in range(V)]  # list of (neighbor, parity), parity 0=equality,1=inequality
        def add(u,v,p): adj[u].append((v,p)); adj[v].append((u,p))
        # Equalities B[P[i]] == T[i]
        for i in range(N):
            add(i, N + P[i], 0)
        # Inequalities within pairs
        for k in range(0, N, 2):
            add(k, k+1, 1)       # T[2k] != T[2k+1]
            add(N+k, N+k+1, 1)   # B[2k] != B[2k+1]
        val = [-1]*V
        for u in range(V):
            if val[u] != -1: continue
            val[u] = 0
            dq = deque([u])
            while dq:
                x = dq.popleft()
                for y,p in adj[x]:
                    want = val[x] ^ p
                    if val[y] == -1:
                        val[y] = want
                        dq.append(y)
                    else:
                        # consistency check
                        assert val[y] == want
        T = val[:N]
        B = val[N:]
        # sanity
        for k in range(0, N, 2):
            assert T[k] ^ T[k+1] == 1
            assert B[k] ^ B[k+1] == 1
        for i in range(N):
            assert B[P[i]] == T[i]
        return T,B

    def compile_controls(self, P: List[int]) -> List[List[int]]:
        if len(P) != self.N or sorted(P) != list(range(self.N)):
            raise ValueError("P must be a permutation 0..N-1")
        ctrls = [[] for _ in range(self.S)]
        self._compile_rec(0, self.N, 0, self.S-1, P, ctrls)
        for s, st in enumerate(self.stages):
            assert len(ctrls[s]) == len(st.switches)
        return ctrls

    def _compile_rec(self, base, N, sf, sl, P, ctrls):
        if N == 1: return
        if N == 2:
            ctrls[sf].append(0 if P[0]==0 else 1)
            return
        T,B = self._assign_TB(P)
        # first-stage controls
        for i in range(N//2):
            a = 2*i
            ctrls[sf].append(1 if T[a]==1 else 0)
        # build sub-perms
        idx_top_in, idx_bot_in = {}, {}
        idx_top_out, idx_bot_out = {}, {}
        top_in_order=[]; bot_in_order=[]
        top_out_order=[]; bot_out_order=[]
        for i in range(N//2):
            a,b=2*i,2*i+1
            if T[a]==0:
                idx_top_in[a]=len(top_in_order); top_in_order.append(a)
                idx_bot_in[b]=len(bot_in_order); bot_in_order.append(b)
            else:
                idx_bot_in[a]=len(bot_in_order); bot_in_order.append(a)
                idx_top_in[b]=len(top_in_order); top_in_order.append(b)
        for j in range(N//2):
            c,d=2*j,2*j+1
            if B[c]==0:
                idx_top_out[c]=len(top_out_order); top_out_order.append(c)
                idx_bot_out[d]=len(bot_out_order); bot_out_order.append(d)
            else:
                idx_bot_out[c]=len(bot_out_order); bot_out_order.append(c)
                idx_top_out[d]=len(top_out_order); top_out_order.append(d)
        Pt=[None]*(N//2); Pb=[None]*(N//2)
        for x in range(N):
            y=P[x]
            if T[x]==0:
                Pt[idx_top_in[x]]=idx_top_out[y]
            else:
                Pb[idx_bot_in[x]]=idx_bot_out[y]
        # recurse
        self._compile_rec(base, N//2, sf+1, sl-1, Pt, ctrls)
        self._compile_rec(base+N//2, N//2, sf+1, sl-1, Pb, ctrls)
        # last-stage controls
        for j in range(N//2):
            ctrls[sl].append(0 if B[2*j]==0 else 1)

    def apply(self, data: List[object], ctrls: List[List[int]]) -> List[object]:
        wires = data[:]
        for st, ctrl in zip(self.stages, ctrls):
            wires = st.eval(wires, ctrl)
        return wires

def run_tests(trials=50, N=32):
    cbg = BenesCBGParity(N)
    for t in range(trials):
        data = [f"D{i}" for i in range(N)]
        random.shuffle(data)
        perm = list(range(N)); random.shuffle(perm)
        ctrls = cbg.compile_controls(perm)
        out = cbg.apply(data, ctrls)
        golden = [None]*N
        for i in range(N): golden[perm[i]] = data[i]
        if out != golden:
            print("Mismatch on trial", t)
            return False
    print("All", trials, "trials passed.")
    return True

run_tests(100, 32)
