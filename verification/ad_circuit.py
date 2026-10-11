#!/usr/bin/env python3
"""Fixed low-degree adjacency--degree circuits. No input-dependent gate choices.

The builder sees only N. Evaluation uses I,A,D, integer scalar multiplication,
addition and matrix multiplication. Transposes are compiled by reversing gates;
there is no transpose or coordinate-access gate in the exported circuit.
"""
from __future__ import annotations
import argparse, gzip, json
from collections import Counter
from pathlib import Path
from typing import Any

Matrix = list[list[int]]

def eye(n: int) -> Matrix:
    return [[int(i == j) for j in range(n)] for i in range(n)]

def add(X: Matrix, Y: Matrix) -> Matrix:
    return [[a+b for a,b in zip(x,y)] for x,y in zip(X,Y)]

def scale(c: int, X: Matrix) -> Matrix:
    return [[c*a for a in row] for row in X]

def mul(X: Matrix, Y: Matrix) -> Matrix:
    n=len(X); Z=[[0]*n for _ in range(n)]
    for i,row in enumerate(X):
        for k,a in enumerate(row):
            if a:
                for j,b in enumerate(Y[k]):
                    if b: Z[i][j] += a*b
    return Z

def transpose(X: Matrix) -> Matrix:
    return [list(x) for x in zip(*X)]

def matvec(X: Matrix, v: list[int]) -> list[int]:
    return [sum(a*b for a,b in zip(row,v)) for row in X]

def dot(u: list[int],v: list[int]) -> int:
    return sum(a*b for a,b in zip(u,v))

def validate_tree(A: Matrix, N: int) -> Matrix:
    n=len(A)
    if not (1 <= n <= N) or any(len(row)!=n for row in A):
        raise ValueError('Expected a square adjacency matrix of order 1..N.')
    for i in range(n):
        for j in range(n):
            if A[i][j] not in (0,1) or A[i][j] != A[j][i] or (i==j and A[i][j]):
                raise ValueError('The input must be a simple undirected graph.')
    seen={0}; stack=[0]
    while stack:
        i=stack.pop()
        for j,a in enumerate(A[i]):
            if a and j not in seen: seen.add(j);stack.append(j)
    if len(seen)!=n or sum(map(sum,A))!=2*(n-1):
        raise ValueError('The input must be a connected tree.')
    return [[sum(A[i]) if i==j else 0 for j in range(n)] for i in range(n)]

class Builder:
    def __init__(self,N: int):
        if not isinstance(N,int) or N<1: raise ValueError('N must be positive.')
        self.N=N; self.nodes:list[dict[str,Any]]=[]; self.degrees:list[int]=[]
        self.cache={};self.tc={}
        self.zero=self._node(('zero',),{'op':'zero'},0)
        self.I=self._node(('I',),{'op':'I'},0)
        self.A=self._node(('A',),{'op':'A'},1)
        self.D=self._node(('D',),{'op':'D'},1)
        for i in (self.zero,self.I,self.A,self.D): self.tc[i]=i
    def _node(self,key,desc,degree):
        if key in self.cache: return self.cache[key]
        i=len(self.nodes);self.nodes.append(desc);self.degrees.append(degree);self.cache[key]=i
        return i
    def add(self,a,b):
        if a==self.zero:return b
        if b==self.zero:return a
        return self._node(('add',a,b),{'op':'add','args':[a,b]},max(self.degrees[a],self.degrees[b]))
    def sc(self,c,a):
        if c==0 or a==self.zero:return self.zero
        if c==1:return a
        return self._node(('scale',c,a),{'op':'scale','constant':str(c),'args':[a]},self.degrees[a])
    def mul(self,a,b):
        if a==self.zero or b==self.zero:return self.zero
        if a==self.I:return b
        if b==self.I:return a
        return self._node(('mul',a,b),{'op':'mul','args':[a,b]},self.degrees[a]+self.degrees[b])
    def star(self,a):
        if a in self.tc:return self.tc[a]
        nd=self.nodes[a];args=nd.get('args',[])
        if nd['op']=='add':b=self.add(self.star(args[0]),self.star(args[1]))
        elif nd['op']=='scale':b=self.sc(int(nd['constant']),self.star(args[0]))
        elif nd['op']=='mul':b=self.mul(self.star(args[1]),self.star(args[0]))
        else:raise AssertionError(nd)
        self.tc[a]=b;self.tc[b]=a;return b
    def probes(self):
        kap=self.N*self.N; prev=[self.I]; ans=[self.I]; labels=[(0,0)]
        for k in range(self.N-1):
            cur=[]
            for j in range(k+2):
                z=self.zero
                if j<=k:
                    z=self.mul(self.add(self.D,self.sc(kap*(j-k),self.I)),prev[j])
                if j>0:z=self.add(z,self.sc(kap,self.mul(self.A,prev[j-1])))
                cur.append(z);ans.append(z);labels.append((k+1,j))
            prev=cur
        return ans,labels
    def all_ones(self):
        Ps=[self.I]
        if self.N>=2:Ps.append(self.A)
        if self.N>=3:Ps.append(self.add(self.mul(self.A,self.A),self.sc(-1,self.D)))
        DmI=self.add(self.D,self.sc(-1,self.I))
        for k in range(3,self.N):
            Ps.append(self.add(self.mul(self.A,Ps[-1]),self.sc(-1,self.mul(DmI,Ps[-2]))))
        out=self.zero
        for P in Ps:out=self.add(out,P)
        return out
    def build(self):
        U,labels=self.probes();J=self.all_ones();m=len(U)
        H=self.N**2*(3*self.N**3)**(2*self.N-2);base=2*H+1
        output=self.zero
        # Reverse digit order, so that the final trace is 2 sum base^nu h_nu.
        for S in (self.D,self.A,self.I):
            for i in range(m-1,-1,-1):
                for j in range(m-1,-1,-1):
                    X=self.mul(self.star(U[i]),self.mul(S,U[j]))
                    Y=self.mul(J,X)
                    sym=self.add(Y,self.star(Y))
                    output=self.add(self.sc(base,output),sym)
        assert self.degrees[output]<=3*self.N-2
        return {'format':'integer-AD-DAG-v1','N':self.N,'kappa':self.N**2,
                'radix':str(base),'digit_bound':str(H),'digit_order':'S in [I,A,D], then i, then j',
                'probe_labels':labels,'probe_nodes':U,'all_ones_node':J,
                'nodes':self.nodes,'output':output,'formal_degree':self.degrees[output],
                'matrix_register_dimension':'input order n (no lift)',
                'final_readout':'trace(output), equal to twice the balanced-radix encoding'}

def evaluate(circuit:dict[str,Any],A:Matrix)->tuple[Matrix,dict[str,int]]:
    N=int(circuit['N']);D=validate_tree(A,N);n=len(A);nodes=circuit['nodes'];out=circuit['output']
    uses=Counter()
    for nd in nodes:
        uses.update(nd.get('args',[]))
    uses[out]+=1
    values={};peakbits=0;peaklive=0
    for i,nd in enumerate(nodes):
        op=nd['op'];args=nd.get('args',[])
        if op=='zero':X=[[0]*n for _ in range(n)]
        elif op=='I':X=eye(n)
        elif op=='A':X=[r[:] for r in A]
        elif op=='D':X=[r[:] for r in D]
        elif op=='add':X=add(values[args[0]],values[args[1]])
        elif op=='scale':X=scale(int(nd['constant']),values[args[0]])
        elif op=='mul':X=mul(values[args[0]],values[args[1]])
        else:raise ValueError(f'Unsupported gate: {op}')
        values[i]=X
        peakbits=max(peakbits,max((abs(a).bit_length() for r in X for a in r),default=0))
        for a in args:
            uses[a]-=1
            if uses[a]==0:values.pop(a,None)
        if uses[i]==0:values.pop(i,None)
        peaklive=max(peaklive,len(values))
    return values[out],{'gates':len(nodes),'peak_entry_bits':peakbits,'peak_live_registers':peaklive}

def direct_probes(A:Matrix,D:Matrix,N:int,v:list[int]|None=None):
    n=len(A);v=[1]*n if v is None else v[:];kap=N*N
    prev=[v];ans=[v[:]]
    for k in range(N-1):
        cur=[]
        for j in range(k+2):
            z=[0]*n
            if j<=k:
                d=matvec(D,prev[j]);z=[a+kap*(j-k)*b for a,b in zip(d,prev[j])]
            if j>0:
                av=matvec(A,prev[j-1]);z=[a+kap*b for a,b in zip(z,av)]
            cur.append(z)
        ans+=cur;prev=cur
    return ans

def direct_digits(A:Matrix,N:int):
    D=validate_tree(A,N);U=direct_probes(A,D,N);digits=[]
    for S in (eye(len(A)),A,D):
        SU=[matvec(S,u) for u in U]
        digits += [dot(u,w) for u in U for w in SU]
    return digits

def encode_digits(digits:list[int],base:int)->int:
    x=0
    for d in reversed(digits):x=x*base+d
    return 2*x

def decode_trace(trace:int,N:int)->list[int]:
    if trace%2:raise ValueError('The trace should be even.')
    H=N*N*(3*N**3)**(2*N-2);base=2*H+1;m=N*(N+1)//2;out=[];x=trace//2
    for _ in range(3*m*m):
        d=(x+H)%base-H;out.append(d);x=(x-d)//base
    if x:raise ValueError('Encoded value exceeds the prescribed digit length.')
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('N',type=int);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();data=Builder(args.N).build();args.output.parent.mkdir(parents=True,exist_ok=True)
    text=json.dumps(data,separators=(',',':'))
    if args.output.suffix=='.gz':
        with gzip.open(args.output,'wt',encoding='utf8') as f:f.write(text)
    else:args.output.write_text(text,encoding='utf8')
    print(json.dumps({'N':args.N,'nodes':len(data['nodes']),'formal_degree':data['formal_degree'],
                      'probes':len(data['probe_nodes']),'output':str(args.output)}))
if __name__=='__main__':main()
