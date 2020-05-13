from sage.all import matrix, vector, GF, random_matrix, random_vector, copy, LinearCode, block_matrix, block_diagonal_matrix, Permutations, identity_matrix

from circuit import CircuitBuilder, Wire, SBOXCircuitBuilder
from generate_matrices import Instance
import unittest
import itertools
import io, pickle
import copy

FF = GF(2)

def Sbox(c, b, a):
    return (a + b + c + a*b, a + b + a*c, a + b*c)

#def S(a, b, c):
    #return (a + b*c, a + b + a*c, a + b + c + a*b)

class LowMC(object):

    def __init__(self, n, k, s, r):
        self.n = n
        self.k = k
        self.s = s
        self.r = r
        self._cb_done = False

        with io.open('matrices_and_constants_{}_{}_{}.pickle'.format(n, k, r), 'rb') as matfile:
            inst = pickle.load(matfile)

        if inst.n != n or inst.k != k or inst.r != r:
            raise ValueError("Unexpected LowMC instance.")

        self.L = [matrix(FF, L) for L in inst.L]
        self.K = [matrix(FF, K) for K in inst.K]
        self.C = [vector(FF, R) for R in inst.R]

    def keygen(self):
        return random_vector(F, self.k)

    def S(self, s):
        for i in range(self.s):
            t = s[3*(i) : 3*(i+1)]
            s[3*(i) : 3*(i+1)] = Sbox(t[0], t[1], t[2])
        return s

    def Ss(self, s):
        a = []
        for i in range(self.s):
            t = s[3*(i) : 3*(i+1)]
            a.append(t[2]*t[1]) #a*b
            a.append(t[2]*t[0]) #a*c
            a.append(t[0]*t[1]) #b*c
            s[3*(i) : 3*(i+1)] = Sbox(t[0], t[1], t[2])
        return s, a

    def enc(self, sk, p):
        s = self.K[0] * sk  + p
        for i in range(self.r):
            s = self.S(s)
            s = self.L[i] * s
            s = self.C[i] + s
            s = self.K[i+1] * sk + s
        return s

    def enc_record_and(self, sk, p):
        ands = []
        s = self.K[0] * sk  + p
        for i in range(self.r):
            s, a = self.Ss(s)
            ands += a
            s = self.L[i] * s
            s = self.C[i] + s
            s = self.K[i+1] * sk + s
        return s, ands

    def _matMul(self, state, mat):
        result = [self.cb.ZERO for _ in range(len(state))]
        for row in range(mat.nrows()):
            for col in range(mat.ncols()):
                if mat[row,col]:
                    result[row] = self.cb.XOR(result[row], (state[col]))
        return result

    def _addConst(self, state, const):
        result = copy.deepcopy(state)
        for i in range(len(state)):
            if const[i]:
                result[i] = self.cb.XOR(result[i], self.cb.ONE)
        return result

    def _sbox(self, state):
        for i in xrange(self.s):
            c,b,a = state[3*(i) : 3*(i+1)]
            state[3*(i) : 3*(i+1)] = (self.cb.XOR(a, self.cb.XOR(b, self.cb.XOR(c, self.cb.AND(a,b)))),
                                    self.cb.XOR(a, self.cb.XOR(b, self.cb.AND(a,c))),
                                    self.cb.XOR(a, self.cb.AND(b,c)))
        return state

    def buildCircuit(self, p, c):
        self.cb = CircuitBuilder()
        sk = [self.cb.addInputWire() for _ in range(self.k)]
        state = self._matMul(sk, self.K[0])
        state = self._addConst(state, p)
        for i in range(self.r):
            state = self._sbox(state)
            state = self._matMul(state, self.L[i])
            state = self._addConst(state, self.C[i])
            roundkey = self._matMul(sk, self.K[i+1])
            state = [self.cb.XOR(a,b) for a,b in zip(state, roundkey)]
        for i in range(self.n):
            self.cb.addOutputWire(state[i], c[i])
        self._cb_done = True


    def getMRHS(self):
        if not self._cb_done:
            return None

        Ms = []
        Ss = []
        size = self.cb.currentId
        for a,b,c in self.cb.andGates:
            A = vector(FF, size)
            B = vector(FF, size)
            C = vector(FF, size)
            for i in a.variables:
                if i == -1: continue
                A[i] = 1
            for i in b.variables:
                if i == -1: continue
                B[i] = 1
            for i in c.variables:
                if i == -1: continue
                C[i] = 1

            Sa = vector(FF, [0,0,1,1])
            Sb = vector(FF, [0,1,0,1])
            Sc = vector(FF, [0,0,0,1])
            if -1 in a.variables:
                Sa += vector(FF, [1,1,1,1])
            if -1 in b.variables:
                Sb += vector(FF, [1,1,1,1])
            if -1 in c.variables:
                Sc += vector(FF, [1,1,1,1])

            Ms.append(A)
            Ms.append(B)
            Ms.append(C)
            Ss.append(Sa)
            Ss.append(Sb)
            Ss.append(Sc)

        # generate output linear equations
        outputMat = matrix(FF, 0, size+1)
        for wire, val in self.cb.outputWires:
            row = vector(FF, size+1)
            #print wire.variables, val
            #input()
            for i in wire.variables:
                if i == -1: continue
                row[i] = 1
            row[size] = val
            if -1 in wire.variables:
                row[size] += 1
            outputMat = outputMat.stack(row)

        outputMat = outputMat.rref()
        #print outputMat, "\n"
        outvars = outputMat.column(size)
        outputMat = outputMat.submatrix(0, 0, outputMat.nrows(), outputMat.ncols() - 1)
        # find columns with HW = 1
        cancel = outputMat.pivots()
        keep = tuple(i for i in range(outputMat.ncols()) if i not in cancel)
        #print cancel, keep

        for i in range(len(Ms)):
            for j in range(outputMat.nrows()):
                if Ms[i][cancel[j]] == 1:
                    Ms[i] += outputMat.rows()[j]
                    Ss[i] += vector(FF, [1,1,1,1]) * outvars[j]
        S = []
        for i in range(0, len(Ss), 3):
            S.append(matrix(FF, [Ss[i], Ss[i + 1], Ss[i + 2]]).transpose())


        M = matrix(FF,Ms).transpose()
        #print M , "\n"
        check = M[cancel,:]
        #print check
        assert check == matrix(FF, check.nrows(), check.ncols())
        M = M[keep,:]
        print "M, Dim:", M.dimensions(), "Rank:", M.rank()
        #print M.transpose()
        return M, S, (outvars, outputMat, M)


    def getDecodingProblem(self, M, S):
        n = M.ncols()
        k = M.nrows()
        si = 4
        ni = 3
        m = n / ni

        C = LinearCode(M)
        #G = C.generator_matrix_systematic()
        H = C.parity_check_matrix()
        print "H, Dim:", H.dimensions(), "Rank:", H.rank()
        #print H.transpose()

        Sbd = block_diagonal_matrix(S, subdivide=False)

        R = Sbd * H.transpose()
        print "R, Dim:", R.dimensions(), "Rank:", R.rank()

        #construct T to transform V to U
        T0 = matrix(FF, si-1, si)
        for i in range(si-1):
            T0[i,0] = 1
            T0[i,i+1] = 1

        T1 = matrix(FF, 1, si)
        T1[0,0] = 1

        # m blocks T0
        T2 = block_diagonal_matrix([T0 for i in range(0,m)],subdivide=False)

        # m blocks T1
        T3 = block_matrix(1,m,[T1 for i in range(0,m)],subdivide=False)

        T = block_matrix(2,1,[T3,T2])

        #final parity check matrix, first row is syndrome
        Q=(T*R)
        print "Q, Dim:", Q.dimensions(), "Rank:", Q.rank()

        return Q

class TestLowMC(unittest.TestCase):

    def test_lowmc_128_128_10_20(self):
        k = '10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        p = '11111111110101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        e = '10110011001010101000100011010010101100001000011001000000111010001100100010111111001101001110001101100111101010111100001010010010'

        k = vector(FF, [int(x) for x in k])
        p = vector(FF, [int(x) for x in p])
        e = vector(FF, [int(x) for x in e])

        lowmc = LowMC(128, 128, 10, 20)
        self.assertEqual(lowmc.enc(k, p), e)

    def test_lowmc_126_126_42_4(self):
        k = '100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        p = '111111111101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        e = '100111010011111101011110111101010010010110111101001110101100011011100010100001010010111011010100110011001000111000111100010110'

        k = vector(FF, [int(x) for x in k])
        p = vector(FF, [int(x) for x in p])
        e = vector(FF, [int(x) for x in e])

        lowmc = LowMC(126, 126, 42, 4)
        self.assertEqual(lowmc.enc(k, p), e)

    def test_lowmc_15_15_5_4(self):
        k = '100000000000000'
        p = '111111111101010'
        e = '010101011011111'

        k = vector(FF, [int(x) for x in k])
        p = vector(FF, [int(x) for x in p])
        e = vector(FF, [int(x) for x in e])

        lowmc = LowMC(15, 15, 5, 4)
        self.assertEqual(lowmc.enc(k, p), e)

    def test_lowmc_128_128_10_20_circuit(self):
        return
        k = '10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        p = '11111111110101010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        e = '10110011001010101000100011010010101100001000011001000000111010001100100010111111001101001110001101100111101010111100001010010010'

        k = vector(FF, [int(x) for x in k])
        p = vector(FF, [int(x) for x in p])
        e = vector(FF, [int(x) for x in e])

        lowmc = LowMC(128, 128, 10, 20)
        self.assertEqual(lowmc.enc(k, p), e)
        lowmc.buildCircuit(p,e)

    def test_lowmc_126_126_42_4_circuit(self):
        k = '100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        p = '111111111101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000'
        e = '100111010011111101011110111101010010010110111101001110101100011011100010100001010010111011010100110011001000111000111100010110'

        k = vector(FF, [int(x) for x in k])
        p = vector(FF, [int(x) for x in p])
        e = vector(FF, [int(x) for x in e])

        lowmc = LowMC(126, 126, 42, 4)
        self.assertEqual(lowmc.enc(k, p), e)
        lowmc.buildCircuit(p,e)
        lowmc.getMRHS()



## Decoding algorithm
def hw(vec):
    return sum(1 for x in vec if x==1)

def final_check_conflicts(lst, num_blocks):
    syndrome = lst[3]
    pos1 = lst[0]
    pos2 = lst[1]

    #syndrome cannot have 1 in positions x[0] and x[1]
    if pos1 != '.' and (syndrome[pos1%num_blocks] == 1 or syndrome[pos1%num_blocks+num_blocks] == 1): return False
    if pos2 != '.' and (syndrome[pos2%num_blocks] == 1 or syndrome[pos2%num_blocks+num_blocks] == 1): return False
    return True

def extract_solution(sols, up, S, num_blocks, outStuff):
    #sols := [ sol ]
    # sol := (ix1, ix2, count, syndrome)
    #up   := [rev]
    #rev  := (block, solnum, row)
    posx = [0] * num_blocks
    s = up[3*num_blocks][2]
    Sbd = block_diagonal_matrix(S, subdivide=False)
    for sol in sols:
        if (sol[0] != '.'):
            posx[ up[sol[0]][0] ] = up[sol[0]][1]
            s += up[sol[0]][2]
        if (sol[1] != '.'):
            posx[ up[sol[1]][0] ] = up[sol[1]][1]
            s += up[sol[1]][2]
        for ix, val in enumerate(sol[3]):
            if val == 1:
                posx[ up[ix][0] ] = up[ix][1]
                s += up[ix][2]

        print sol
        print s
        print posx
        rhs = []
        for i in range(num_blocks):
            rhs += list(Sbd[4*i+posx[i]][3*i:3*i+3])
            #rhs.append(Sbd[4*i+posx[i]][3*i+2])

        rhs = vector(FF, rhs)
        M = outStuff[2]
        res = M.solve_left(rhs)
        print res
        #print rhs

        outputMat = outStuff[1]
        outvars = outStuff[0]
        cancel = outputMat.pivots()
        keep = tuple(i for i in range(outputMat.ncols()) if i not in cancel)
        #extended = vector(FF, outputMat.ncols())
        extended = vector(FF, outputMat.ncols())
        for e,i in enumerate(keep):
            extended[i] = res[e]
        #print "ext", extended
        #mat = outputMat[:,keep]
        #print outputMat
        #print mat
        #print outputMat[:,cancel]
        missing = outputMat * extended + outvars
        #print missing
        sol = []
        j, k = 0,0
        for i in range(outputMat.ncols()):
            if i in cancel:
                sol.append(missing[j])
                j +=1
            else:
                sol.append(res[k])
                k +=1

        print sol
        return sol

def extract_solution_other(sols, up, S, num_blocks, outStuff):
    #sols := [ sol ]
    # sol := (ix1, ix2, count, syndrome)
    #up   := [rev]
    #rev  := (block, solnum, row)
    posx = [0] * num_blocks
    s = up[6*num_blocks][2]
    Sbd = block_diagonal_matrix(S, subdivide=False)
    for sol in sols:
        if (sol[0] != '.'):
            posx[ up[sol[0]][0] ] = up[sol[0]][1]
            s += up[sol[0]][2]
        if (sol[1] != '.'):
            posx[ up[sol[1]][0] ] = up[sol[1]][1]
            s += up[sol[1]][2]
        for ix, val in enumerate(sol[3]):
            if val == 1:
                posx[ up[ix][0] ] = up[ix][1]
                s += up[ix][2]

        print sol
        print s
        print posx
        rhs = []
        for i in range(num_blocks):
            rhs += list(Sbd[8*i+posx[i]][6*i:6*i+6])
            #rhs.append(Sbd[4*i+posx[i]][3*i+2])

        rhs = vector(FF, rhs)
        M = outStuff[2]
        res = M.solve_left(rhs)
        print res
        #print rhs

        outputMat = outStuff[1]
        outvars = outStuff[0]
        cancel = outputMat.pivots()
        keep = tuple(i for i in range(outputMat.ncols()) if i not in cancel)
        #extended = vector(FF, outputMat.ncols())
        extended = vector(FF, outputMat.ncols())
        for e,i in enumerate(keep):
            extended[i] = res[e]
        #print "ext", extended
        #mat = outputMat[:,keep]
        #print outputMat
        #print mat
        #print outputMat[:,cancel]
        missing = outputMat * extended + outvars
        #print missing
        sol = []
        j, k = 0,0
        for i in range(outputMat.ncols()):
            if i in cancel:
                sol.append(missing[j])
                j +=1
            else:
                sol.append(res[k])
                k +=1

        print sol
        return sol


#adapted version of Lee-Brickel decoding
def decoding(U, S, outMatrix, max_try = 1000000):

    u=U.rows()[0]

    num_blocks = (U.nrows() - 1) / 3

    count = 0
    while count < max_try:

        count += 1

        #apply random permutation to blocks, and separate columns
        P=Permutations(num_blocks).random_element()

        up = [None] * (3*num_blocks+1)
        for i in range(num_blocks):
            R = Permutations(3).random_element()
            for j in range(3):
                up[num_blocks*j + i] = (P[i]-1, R[j], U.rows()[1+(P[i]-1)*3+R[j]-1])
        up[3*num_blocks] = ('.', '.', u)

        #create echelon form, last block has each vector from a different block
        UP = matrix(GF(2),map(lambda x: x[2], up)).transpose().echelon_form().transpose()
        if UP[0:num_blocks*2,0:num_blocks*2] != identity_matrix(num_blocks*2):
            continue


        #create a list of potential solutions including at most 2 vectors from the last block
        l1 = [[i,UP.rows()[i]] for i in range(num_blocks*2,num_blocks*3)]
        uhat = UP.rows()[num_blocks*3]
        lst = [('.','.',0,uhat)]+[(x[0],'.',1,uhat+x[1]) for x in l1]+[(x[0],y[0],2,uhat+x[1]+y[1]) for x in l1 for y in l1 if y[0] > x[0]]

        # filter by weight
        weight_ok = filter(lambda x: hw(x[3])+x[2] <= num_blocks, lst)
        # then by conflicts in the first two blocks
        no_conflicts12 = filter(lambda x: sum(1 if x[3][i]==1 and x[3][num_blocks+i]==1 else 0 for i in range(num_blocks)) < 1, weight_ok)
        no_conflicts = filter(lambda x : final_check_conflicts(x, num_blocks), no_conflicts12)
        if len(no_conflicts) > 0:
            #print UP.str()
            #print no_conflicts
            print "count:", count
            return extract_solution(no_conflicts, up, S, num_blocks, outMatrix)
    print "out of tries :("


def brute_lowmc_key(lowmc, p, e):
    klen = lowmc.k

    possible_keys_gen = ( vector(FF, x) for x in itertools.product( (0,1), repeat=klen))

    for keyguess in possible_keys_gen:
        if lowmc.enc(keyguess, p) == e:
            yield keyguess


def test_15bit():
    k = '100000000000000'
    p = '111111111101000'
    e = '001110100001001'

    k = vector(FF, [int(x) for x in k])
    p = vector(FF, [int(x) for x in p])
    e = vector(FF, [int(x) for x in e])

    lowmc = LowMC(15, 15, 5, 4)
    print lowmc.enc(k,p)
    #assert lowmc.enc(k,p) == e

    import time
    start = time.time()
    for kg in brute_lowmc_key(lowmc, p, e):
        assert lowmc.enc(kg, p) == e
    dur = time.time() -start
    print "Brute:", dur/2


    times = []
    trials = 10
    for i in range(trials):
        k = matrix(FF, 1, 15)
        k.randomize()
        k = k.rows()[0]
        p = matrix(FF, 1, 15)
        p.randomize()
        p = p.rows()[0]
        e = lowmc.enc(k,p)

        lowmc.buildCircuit(p,e)
        M, S, outMatrix = lowmc.getMRHS()
        #print G, S
        Q = lowmc.getDecodingProblem(M, S)

        start = time.time()
        sol = decoding(Q, S, outMatrix)
        dur = time.time() -start
        print "Dec:", dur
        times.append(dur)
        _, ands = lowmc.enc_record_and(k,p)
        correct = vector(FF, list(k) + ands)
        try:
            recoveredkey = vector(FF, sol[0:lowmc.k])
            print "recovered key is ", lowmc.enc(recoveredkey, p) == e
        except Exception as e:
            print e
    print "Avg:", sum(times)/trials

def test_21bit():
    k = '100000000000000000000'
    p = '111111111101000000000'
    e = '101000001010010101001'

    k = vector(FF, [int(x) for x in k])
    p = vector(FF, [int(x) for x in p])
    e = vector(FF, [int(x) for x in e])

    lowmc = LowMC(21, 21, 7, 3)
    k = matrix(FF, 1, 21)
    k.randomize()
    k = k.rows()[0]
    p = matrix(FF, 1, 21)
    p.randomize()
    p = p.rows()[0]
    e = lowmc.enc(k,p)
    print lowmc.enc(k,p)
    #assert lowmc.enc(k,p) == e

    import time
    start = time.time()
    for kg in brute_lowmc_key(lowmc, p, e):
        assert lowmc.enc(kg, p) == e
    dur = time.time() -start
    print "Brute:", dur/2
    for i in range(10):
        k = matrix(FF, 1, 21)
        k.randomize()
        k = k.rows()[0]
        p = matrix(FF, 1, 21)
        p.randomize()
        p = p.rows()[0]
        e = lowmc.enc(k,p)
        lowmc.buildCircuit(p,e)
        M, S, outMatrix = lowmc.getMRHS()
        #print G, S
        Q = lowmc.getDecodingProblem(M, S)

        startdec = time.time()
        sol = decoding(Q, S, outMatrix)
        dur = time.time() -startdec
        print dur #

        _, ands = lowmc.enc_record_and(k,p)
        try:
            recoveredkey = vector(FF, sol[0:lowmc.k])
            print "recovered key is ", lowmc.enc(recoveredkey, p) == e
        except Exception as e:
            print e

if __name__ == '__main__':
    #unittest.main()
    test_15bit()


