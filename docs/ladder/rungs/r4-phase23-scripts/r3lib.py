"""Rank retention for multiplication by indicators of F_p-affine subspaces on low-degree
multilinear polynomials modulo a PC consequence space C_D.  Everything is done in the FUNCTION
basis (values on the cube {0,1}^n); V_K = span of monomial functions of degree <= K.
Research scratch for docs/ladder/rungs/r4-phase23-r3.md."""
import itertools, math, random
import numpy as np

def rank_mod(M, p):
    """rank of integer matrix mod p (destroys copy)"""
    M = (np.array(M, dtype=np.int64) % p)
    if M.size == 0: return 0
    r = 0; rows, cols = M.shape
    for c in range(cols):
        if r >= rows: break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0: continue
        k = r + nz[0]
        if k != r: M[[r, k]] = M[[k, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        idx = np.nonzero(M[r + 1:, c])[0] + r + 1
        if idx.size: M[idx] = (M[idx] - np.outer(M[idx, c], M[r])) % p
        r += 1
    return r

def rref_mod(M, p):
    M = (np.array(M, dtype=np.int64) % p); r = 0; piv = []
    rows, cols = M.shape
    for c in range(cols):
        if r >= rows: break
        nz = np.nonzero(M[r:, c])[0]
        if nz.size == 0: continue
        k = r + nz[0]
        if k != r: M[[r, k]] = M[[k, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        idx = np.nonzero(M[:, c])[0]; idx = idx[idx != r]
        if idx.size: M[idx] = (M[idx] - np.outer(M[idx, c], M[r])) % p
        piv.append(c); r += 1
    return M[:r], piv

class Cube:
    def __init__(s, n, p):
        s.n = n; s.p = p; s.N = 1 << n
        s.pts = np.arange(s.N)
        s.bits = np.array([(s.pts >> i) & 1 for i in range(n)])      # n x 2^n
        s.pc = np.array([bin(m).count('1') for m in range(s.N)])
    def monos(s, K):
        return [m for m in range(s.N) if s.pc[m] <= K]
    def monofun(s, m):
        """values of monomial x^m on the cube"""
        return ((s.pts & m) == m).astype(np.int64)
    def Vbasis(s, K):
        return np.array([s.monofun(m) for m in s.monos(K)], dtype=np.int64)
    def NK(s, K): return sum(math.comb(s.n, j) for j in range(0, K + 1))
    def form(s, a, a0):
        return (a0 + np.tensordot(np.array(a), s.bits, axes=1)) % s.p
    def indicator(s, forms):
        """0/1 indicator of {all forms vanish}; forms = list of (a-vector, a0)"""
        g = np.ones(s.N, dtype=np.int64)
        for a, a0 in forms:
            g = g * (s.form(a, a0) == 0)
        return g
    def to_coef(s, f):
        """Mobius transform mod p: function values -> multilinear coefficients"""
        c = f.copy() % s.p
        for i in range(s.n):
            b = 1 << i
            hi = (s.pts & b) != 0
            c[hi] = (c[hi] - c[s.pts[hi] ^ b]) % s.p
        return c
    def to_val(s, c):
        f = c.copy() % s.p
        for i in range(s.n):
            b = 1 << i
            hi = (s.pts & b) != 0
            f[hi] = (f[hi] + f[s.pts[hi] ^ b]) % s.p
        return f
    def degree(s, f):
        c = s.to_coef(f); nz = np.nonzero(c)[0]
        return 0 if nz.size == 0 else int(s.pc[nz].max())

class Quot:
    """quotient of function space by a subspace C (given as rows of function values)"""
    def __init__(s, cube, Crows):
        s.cube = cube; p = cube.p
        if Crows is None or len(Crows) == 0:
            s.R = np.zeros((0, cube.N), dtype=np.int64); s.piv = []
        else:
            s.R, s.piv = rref_mod(Crows, p)
        s.dim = len(s.piv)
    def reduce(s, V):
        if s.dim == 0: return V % s.cube.p
        p = s.cube.p
        return (V - V[:, s.piv] @ s.R) % p

def stack_rank(cube, Q, K, P, gs):
    """c_P(K): rank of f -> (P g_i f)_i on V_K into (V/C)^s ; P a function (values), gs list of functions"""
    p = cube.p
    B = cube.Vbasis(K)
    blocks = [Q.reduce((B * (P * g)[None, :]) % p) for g in gs]
    return rank_mod(np.concatenate(blocks, axis=1), p)

def span_combos(s, p):
    """one representative per projective point of F_p^s"""
    out = []
    for c in itertools.product(range(p), repeat=s):
        nz = [x for x in c if x]
        if nz and nz[0] == 1: out.append(c)
    return out

def Pprime(cube, gs, c):
    q = sum(ci * g for ci, g in zip(c, gs)) % cube.p
    return (q == 0).astype(np.int64)      # = 1 - q^(p-1) on the cube
