# Decoding Attack on LowMC


Implementation of a syndrome decoding attack on LowMC. Based on [Pavol Zajac's Attack on SIMON-32](https://github.com/zajacpa/DecodingAttack) and the accompanying paper [1].


[1] Zajac, P. Upper bounds on the complexity of algebraic cryptanalysis of ciphers with a low multiplicative complexity. Des. Codes Cryptogr. 82, 43–56 (2017). https://doi.org/10.1007/s10623-016-0256-x,


## Usage

First, generate the necessary LowMC constants (e.g., for a state size of 21 bits and a key size of 21 bits and 4 rounds), afterwards call the attack script (which has internal functions for different sizes).

```
sage -python ./generate_matrices.py 21 21 4
sage -python ./lowmc.py 
```

