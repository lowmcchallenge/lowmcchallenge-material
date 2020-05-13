#! /usr/bin/env sage

from sage.all import GF, matrix
from six.moves import range
import pickle
import io


F = GF(2)


class Instance(object):
    def __init__(self, n, k, r, L, K, R):
        self.n = n
        self.k = k
        self.r = r
        self.L = L
        self.K = K
        self.R = R


def main(blocksize=256, keysize=256, rounds=19):
    ''' Use the global parameters `blocksize`, `keysize` and `rounds`
        to create the set of matrices and constants for the corresponding
        LowMC instance. Save those in a file named
        `matrices_and_constants.dat`.
    '''
    gen = grain_ssg()
    linlayers = []
    for _ in range(rounds):
        linlayers.append(instantiate_matrix(blocksize, blocksize, gen))

    round_constants = []
    for _ in range(rounds):
        constant = [next(gen) for _ in range(blocksize)]
        round_constants.append(constant)

    roundkey_matrices = []
    for _ in range(rounds + 1):
        mat = instantiate_matrix(blocksize, keysize, gen)
        roundkey_matrices.append(mat)

    inst = Instance(blocksize, keysize, rounds, linlayers, roundkey_matrices,
            round_constants)
    with io.open('matrices_and_constants_{}_{}_{}.pickle'.format(blocksize, keysize, rounds), 'wb') as matfile:
        pickle.dump(inst, matfile, protocol=2)


def instantiate_matrix(n, m, gen):
    ''' Instantiate a matrix of maximal rank using bits from the
        generatator `gen`.
    '''
    while True:
        mat = []
        for _ in range(n):
            row = []
            for _ in range(m):
                row.append(next(gen))
            mat.append(row)
        sagem = matrix(F, mat)
        if sagem.rank() >= min(n, m):
            return mat


def grain_ssg():
    ''' A generator for using the Grain LSFR in a self-shrinking generator. '''
    state = [1] * 80
    index = 0
    # Discard first 160 bits
    for _ in range(160):
        state[index] ^= state[(index + 13) % 80] ^ state[(index + 23) % 80]\
                        ^ state[(index + 38) % 80] ^ state[(index + 51) % 80]\
                        ^ state[(index + 62) % 80]
        index += 1
        index %= 80
    choice = False
    while True:
        state[index] ^= state[(index + 13) % 80] ^ state[(index + 23) % 80]\
                        ^ state[(index + 38) % 80] ^ state[(index + 51) % 80]\
                        ^ state[(index + 62) % 80]
        choice = state[index]
        index += 1
        index %= 80
        state[index] ^= state[(index + 13) % 80] ^ state[(index + 23) % 80]\
                        ^ state[(index + 38) % 80] ^ state[(index + 51) % 80]\
                        ^ state[(index + 62) % 80]
        if choice == 1:
            yield state[index]
        index += 1
        index %= 80


if __name__ == '__main__':
    import sys

    if len(sys.argv) == 4:
        blocksize, keysize, rounds = map(int, sys.argv[1:4])
        main(blocksize, keysize, rounds)
    else:
        main()
