############################################################
### Imports (minimal!)
############################################################

from datetime import datetime
from os import urandom
from sys import stdout, stderr, argv
from socket import socket

############################################################
### Utilities
############################################################

# simple things we could have implemented, but these are much faster
from operator import xor
from functools import reduce

BASE64_LOOKUP = bytes(
    i - 0x41 if 0x41 <= i <= 0x5A else
    i - 0x47 if 0x61 <= i <= 0x7A else
    i + 0x04 if 0x30 <= i <= 0x39 else
    0x3E if i == 0x2B else
    0x3F if i == 0x2F else
    0xFF for i in range(256))

def rotl32(x, bits):
    return (x << bits | x >> (32 - bits)) & 0xFFFFFFFF

def rotr32(x, bits):
    return (x << (32 - bits) | x >> bits) & 0xFFFFFFFF

def rotl64(x, bits):
    return (x << bits | x >> (64 - bits)) & 0xFFFFFFFFFFFFFFFF

def rotr64(x, bits):
    return (x << (64 - bits) | x >> bits) & 0xFFFFFFFFFFFFFFFF

def only_or_none(x):
    if x is not None:
        [x] = x
    return x

def urandom_nonzero(count):
    b = bytearray()
    while len(b) < count:
        a = urandom(16)
        if all(a): b += a
    return b[:count]

def xor_bytes(a, b):
    l = len(a)
    assert l == len(b)
    return (int.from_bytes(a, 'little') ^
            int.from_bytes(b, 'little')).to_bytes(l, 'little')

def create_reader(buf):
    mv = memoryview(buf)
    def read(n):
        nonlocal mv
        res, mv = partition_data(mv, n, False)
        return bytes(res)
    return read

def min_bytes_for_int(x):
    return (x.bit_length() + 7) // 8

def split_url(url):
    ss = url[url.index('://')+3:]
    result = ss.split('/', 1)
    if len(result) == 1:
        hostname, path = result[0], ''
    else:
        hostname, path = result
    return hostname, '/' + path

def host_match(hostname, pattern):
    if pattern.startswith('*.'):
        return hostname.endswith(pattern[1:])
    else:
        return hostname == pattern

def partition_data(data, pos, verify=True):
    a, b = data[:pos], data[pos:]
    if verify and (len(a) != pos if pos >= 0 else len(b) != -pos):
        raise ValueError('data too small')
    return a, b

def consume_front(seq, n):
    res = seq[:n]
    del seq[:n]
    return res

def base64_decode(inp):
    lookup = BASE64_LOOKUP
    inl, out = len(inp), bytearray()
    if inl % 4: raise ValueError('input must have length multiple of 4')
    neq = next(i for i, x in enumerate(reversed(inp)) if x != 0x3D)
    if neq > 2: raise ValueError('too much padding')
    inp = inp[:inl-neq] + b'A' * neq
    for i in range(0, inl, 4):
        a, b, c, d = ts = inp[i:i+4].ljust(4, b'A').translate(lookup)
        if 0xFF in ts: raise ValueError('invalid character found')
        out += (a << 18 | b << 12 | c << 6 | d).to_bytes(3, 'big')
    return bytes(out[:len(out)-neq])

############################################################
### Binary structure helpers
############################################################

class StructureDict(dict):
    def __init__(self):
        self.order = []
    def __setitem__(self, key, value):
        key in self and self.order.remove(key)
        super().__setitem__(key, value)
        self.order.append(key)
    def __delitem__(self, key):
        super().__delitem__(key)
        self.order.remove(key)

class StructureMeta(type):
    def __prepare__(self, bases):
        return StructureDict()
    def __new__(cls, name, bases, attrs):
        all_fields = []
        for field_name in attrs.order:
            field = attrs[field_name]
            if isinstance(field, Field):
                field._name = field_name
                all_fields.append(field)
        new_cls = type.__new__(cls, name, bases, attrs)
        new_cls._fields = tuple(all_fields)
        return new_cls

class Field(object):
    def __get__(self, instance, owner):
        return instance.__dict__[self._name]
    def __set__(self, instance, value):
        instance.__dict__[self._name] = value

class Structure(Field, metaclass=StructureMeta):
    _fields = ()
    def __init__(self, **kwds):
        for field in self._fields:
            setattr(self, field._name, kwds.pop(field._name, None))
        if kwds:
            raise ValueError('unknown fields: ' + repr(kwds))
    def __repr__(self):
        return '{}({})'.format(self.__class__.__name__,
                               ', '.join('{}={}'.format(field._name, getattr(self, field._name))
                                         for field in self._fields))
    def __bytes__(self):
        return b''.join(field._encode(getattr(self, field._name))
                        for field in self._fields)
    @staticmethod
    def _create_reader_with_remaining(buf):
        mv = memoryview(buf)
        def read(n):
            nonlocal mv
            res, mv = partition_data(mv, n)
            return bytes(res)
        return read, (lambda: len(mv))
    @classmethod
    def _decode_structure_from_rr(cls, read, remaining, exact):
        res = cls()
        for field in res._fields:
            setattr(res, field._name, field._decode(read, remaining))
        if exact and remaining():
            raise ValueError('extraneous data found')
        return res
    @classmethod
    def decode_structure_from_bytes(cls, data):
        read, remaining = Structure._create_reader_with_remaining(data)
        return cls._decode_structure_from_rr(read, remaining, True)
    @classmethod
    def decode_structure_from_stream(cls, read):
        remaining = lambda: 0xFFFFFFFF
        return cls._decode_structure_from_rr(read, remaining, False)

    class Integer(Field):
        def __init__(self, length):
            self.length = length
        def _encode(self, value):
            return value.to_bytes(self.length, 'big')
        def _decode(self, read, remaining):
            return int.from_bytes(read(self.length), 'big')
    class FixedString(Field):
        def __init__(self, length):
            self.length = length
        def _encode(self, value):
            if len(value) != self.length:
                raise ValueError('must be of length {}')
            return value
        def _decode(self, read, remaining):
            return read(self.length)
    class VariableString(Field):
        def __init__(self, min_length, max_length):
            self.min_length, self.max_length = min_length, max_length
            self.int_size = min_bytes_for_int(max_length)
        def _encode(self, value):
            a, b, l = self.min_length, self.max_length, len(value)
            if not (a <= l <= b):
                raise ValueError('must be of length {}-{}'.format(a, b))
            return l.to_bytes(self.int_size, 'big') + value
        def _decode(self, read, remaining):
            a, b, l = self.min_length, self.max_length, int.from_bytes(read(self.int_size), 'big')
            if not (a <= l <= b):
                raise ValueError('incoming data has invalid length {}'.format(l))
            return read(l)
    class Multiple(VariableString):
        def __init__(self, base_type, min_length, max_length, optional=False):
            super().__init__(min_length, max_length)
            self.base_type, self.optional = base_type, optional
        def _encode(self, value):
            if self.optional and len(value) == 0: return b''
            return super()._encode(b''.join(self.base_type._encode(x) for x in value))
        def _decode(self, read, remaining):
            if self.optional and remaining() == 0: return []
            res, data = [], super()._decode(read, remaining)
            read, remaining = Structure._create_reader_with_remaining(data)
            while remaining(): res.append(self.base_type._decode(read, remaining))
            return res
    class SubStructure(Field):
        def __init__(self, struct_type):
            self.struct_type = struct_type
        def _encode(self, value):
            return bytes(value)
        def _decode(self, read, remaining):
            return self.struct_type._decode_structure_from_rr(read, remaining, False)

TLS_RECORD_MAX_SIZE = 16384

class TLSPre:
    class HelloExtension(Structure):
        extension_type = Structure.Integer(2)
        extension_data = Structure.VariableString(0, 2**16 - 1)
    class ServerDHParams(Structure):
        dh_p                  = Structure.VariableString(1, 2**16 - 1)
        dh_g                  = Structure.VariableString(1, 2**16 - 1)
        dh_Ys                 = Structure.VariableString(1, 2**16 - 1)
    class ServerECDHParams(Structure):
        curve_type            = Structure.Integer(1)
        namedcurve            = Structure.Integer(2)
        public                = Structure.VariableString(1, 2**8 - 1)
    class ServerName(Structure):
        name_type             = Structure.Integer(1)
        host_name             = Structure.VariableString(1, 2**16 - 1)

class TLSStructures:
    global TLSPre
    class TLSRecord(Structure):
        type                  = Structure.Integer(1)
        protocol_version      = Structure.Integer(2)
        fragment              = Structure.VariableString(0, TLS_RECORD_MAX_SIZE + 2048)
    class PreMasterSecret(Structure):
        client_version        = Structure.Integer(2)
        random                = Structure.FixedString(46)
    class MACCalculationHeader(Structure):
        seq_num               = Structure.Integer(8)
        type                  = Structure.Integer(1)
        version               = Structure.Integer(2)
        length                = Structure.Integer(2)
    class ServerNameIndication(Structure):
        server_name_list      = Structure.Multiple(Structure.SubStructure(TLSPre.ServerName), 1, 2**16 - 1)
    class SupportedSignatureAlgorithms(Structure):
        algos                 = Structure.Multiple(Structure.Integer(2), 2, 2**16 - 2)
    class ClientHello(Structure):
        client_version        = Structure.Integer(2)
        random                = Structure.FixedString(32)
        session_id            = Structure.VariableString(0, 32)
        cipher_suites         = Structure.Multiple(Structure.Integer(2), 2, 2**16 - 2)
        compression_methods   = Structure.Multiple(Structure.Integer(1), 1, 2**8 - 1)
        extensions            = Structure.Multiple(Structure.SubStructure(TLSPre.HelloExtension), 0, 2**16 - 1,
                                                   optional=True)
    class ServerHello(Structure):
        server_version        = Structure.Integer(2)
        random                = Structure.FixedString(32)
        session_id            = Structure.VariableString(0, 32)
        cipher_suite          = Structure.Integer(2)
        compression_method    = Structure.Integer(1)
        extensions            = Structure.Multiple(Structure.SubStructure(TLSPre.HelloExtension), 0, 2**16 - 1,
                                                   optional=True)
    class Certificate(Structure):
        certificate_list      = Structure.Multiple(Structure.VariableString(1, 2**24 - 1), 0, 2**24 - 1)
    class ServerKeyExchangeDHE(Structure):
        params                = Structure.SubStructure(TLSPre.ServerDHParams)
        hash_algo             = Structure.Integer(1)
        sig_algo              = Structure.Integer(1)
        signature             = Structure.VariableString(0, 2**16 - 1)
    class ServerKeyExchangeECDHE(Structure):
        params                = Structure.SubStructure(TLSPre.ServerECDHParams)
        hash_algo             = Structure.Integer(1)
        sig_algo              = Structure.Integer(1)
        signature             = Structure.VariableString(0, 2**16 - 1)
    class ClientKeyExchangeRSA(Structure):
        enc_pre_master_secret = Structure.VariableString(0, 2**16 - 1)
    class ClientKeyExchangeDHE(Structure):
        dh_Yc                 = Structure.VariableString(1, 2**16 - 1)
    class ClientKeyExchangeECDHE(Structure):
        ecdh_Yc               = Structure.VariableString(1, 2**8-1)
    class Finished(Structure):
        verify_data           = Structure.FixedString(12)
    # move everything in TLSPre over to TLSStructures
    locals().update(TLSPre.__dict__)
    del TLSPre

############################################################
### AES
############################################################

AES_POLY = 0x11B

def aes_gf8_mul(a, b):
    aes_poly = AES_POLY # for performance
    r = 0
    while b:
        r ^= -(b & 1) & a   # xor r with a if lower-order bit of b set
        a, b = a << 1, b >> 1
        a ^= -(a >> 8) & aes_poly # xor a with aes_poly with bit 8 set
    return r

def aes_gf8_inv(k):
    return next(x for x in range(256) if aes_gf8_mul(k, x) == 1)

def aes_generate_boxes():
    rotl8 = lambda q, z: (q << z | q >> (8 - z)) & 0xFF
    xfrm  = lambda q: reduce(xor, (rotl8(q, z) for z in range(5))) ^ 0x63
    g     = 3 # x + 1
    g_inv = aes_gf8_inv(g)
    s_fwd, s_rev = [None] * 256, [None] * 256
    a, a_inv = 1, 1
    while True:
        x = xfrm(a_inv)
        s_fwd[a] = x
        s_rev[x] = a
        a, a_inv = aes_gf8_mul(a, g), aes_gf8_mul(a_inv, g_inv)
        if a == 1: break
    [rem] = set(range(256)) - set(s_fwd)
    s_fwd[0], s_rev[rem] = rem, 0
    return bytes(s_fwd), bytes(s_rev)

class AES(object):

    S_FWD, S_REV = aes_generate_boxes()
    M_FWD = tuple(bytes(aes_gf8_mul(i, j) for i in range(256))
                  for j in (0x2, 0x3, 0x1, 0x1))
    M_REV = tuple(bytes(aes_gf8_mul(i, j) for i in range(256))
                  for j in (0xE, 0xB, 0xD, 0x9))
    block_size = 16

    def __init__(self, key):
        if len(key) not in (16, 24, 32):
            raise ValueError('bad key length')
        aes_split_word = lambda word:  word.to_bytes(4, 'big')
        aes_join_word  = lambda parts: int.from_bytes(parts, 'big')
        aes_SubWord = lambda word: aes_join_word(aes_split_word(word).translate(self.S_FWD))
        aes_RotWord = lambda word: (word << 8 | word >> 24) & 0xFFFFFFFF
        wo = [aes_join_word(key[s:s+4]) for s in range(0, len(key), 4)]
        Nk = self.Nk = len(wo)
        Nr = self.Nr = Nk + 6
        rcon = 1
        for i in range(Nk, 4 * (Nr + 1)):
            temp = wo[i-1]
            if i % Nk == 0:
                temp = aes_SubWord(aes_RotWord(temp)) ^ (rcon << 24)
                rcon = aes_gf8_mul(rcon, 2)
            elif Nk > 6 and i % Nk == 4:
                temp = aes_SubWord(temp)
            wo.append(wo[i-Nk] ^ temp)
        w = self.w = []
        for i in range(Nr + 1):
            w.append(b''.join(map(aes_split_word, wo[4*i:4*i+4])))

    def _crypt(self, block, inv):
        if len(block) != 16:
            raise ValueError('bad block length')
        (Nr, AddRoundKey, SubBytes, ShiftRows, MixColumns) = (
            self.Nr, self.AddRoundKey, self.SubBytes, self.ShiftRows, self.MixColumns)
        state = bytes(block)
        state = AddRoundKey(state, Nr if inv else 0)
        for rnd in range(1, Nr)[::-1 if inv else 1]:
            state = SubBytes(state, inv)
            state = ShiftRows(state, inv)
            if inv:
                state = AddRoundKey(state, rnd) # runs on inv
            state = MixColumns(state, inv)
            if not inv:
                state = AddRoundKey(state, rnd) # runs on not inv
        state = SubBytes(state, inv)
        state = ShiftRows(state, inv)
        state = AddRoundKey(state, 0 if inv else Nr)
        return state

    def encrypt(self, block):
        return self._crypt(block, False)

    def decrypt(self, block):
        return self._crypt(block, True)

    def AddRoundKey(self, state, rnd):
        return (int.from_bytes(state, 'little') ^
                int.from_bytes(self.w[rnd], 'little')).to_bytes(16, 'little')

    def SubBytes(self, state, inv):
        tbl = self.S_REV if inv else self.S_FWD
        return state.translate(tbl)

    def ShiftRows(self, state, inv):
        (s00, s10, s20, s30,
         s01, s11, s21, s31,
         s02, s12, s22, s32,
         s03, s13, s23, s33) = state
        if inv:
            return bytes((s00, s13, s22, s31,
                          s01, s10, s23, s32,
                          s02, s11, s20, s33,
                          s03, s12, s21, s30))
        else:
            return bytes((s00, s11, s22, s33,
                          s01, s12, s23, s30,
                          s02, s13, s20, s31,
                          s03, s10, s21, s32))

    def MixColumns(self, state, inv):
        matrx = self.M_REV if inv else self.M_FWD
        nst = bytearray()
        for i in (0, 4, 8, 12):
            ((a0, a1, a2, a3),
             (b0, b1, b2, b3),
             (c0, c1, c2, c3),
             (d0, d1, d2, d3)) = map(state[i:i+4].translate, matrx)
            nst[i:i+4] = (a0 ^ b1 ^ c2 ^ d3,
                          a1 ^ b2 ^ c3 ^ d0,
                          a2 ^ b3 ^ c0 ^ d1,
                          a3 ^ b0 ^ c1 ^ d2)
        return bytes(nst)

############################################################
### AES+GCM
############################################################

def aes_gcm_gen_reduction_table():
    red_table = [0] * 256
    for s in range(8):
        m = 0b11100001 << (113 + s)
        for i in range(256):
            if i & (1 << s):
                red_table[i] ^= m
    return red_table

AES_GCM_REDUCTION_TABLE = aes_gcm_gen_reduction_table()

class AESGCM(object):
    iv_size    = 4
    nonce_size = 8
    tag_size   = 16
    def __init__(self, key, iv):
        self.aes = AES(key)
        self.iv = iv
        self.mult_table = self._gen_mult_table()
    def encrypt(self, nonce, header, fragment):
        fragment, tag = self._crypt(self.iv + nonce, header, fragment, False)
        return fragment + tag
    def decrypt(self, nonce, header, fragment):
        fragment, given_tag = partition_data(fragment, -16)
        fragment, expected_tag = self._crypt(self.iv + nonce, header, fragment, True)
        if given_tag != expected_tag: raise ValueError('bad tag')
        return fragment
    def _gen_mult_table(self):
        m = int.from_bytes(self.aes.encrypt(b'\0' * 16), 'big')
        mult_table = [0] * 256
        for s in reversed(range(8)):
            for i in range(256):
                if i & (1 << s):
                    mult_table[i] ^= m
            m = (m >> 1) ^ ((0b11100001 << 120) * (m & 1))
        return mult_table
    def _crypt(self, iv, addl, data, decrypt):
        int_from_bytes, int_to_bytes = int.from_bytes, int.to_bytes
        enumerate_, reversed_ = enumerate, reversed # cache as closures for performance
        mult_table, red_table = self.mult_table, AES_GCM_REDUCTION_TABLE
        data = bytearray(data)
        hash_state = 0
        Ji = 1
        def hash_block(x):
            nonlocal hash_state
            h = hash_state
            m = 0
            for k, c in enumerate_(reversed_(x.ljust(16, b'\0'))):
                m ^= mult_table[c ^ (h & 0xFF)] << (8 * k)
                h >>= 8
            for k in range(15):
                m = (m >> 8) ^ red_table[m & 0xFF]
            hash_state = m
        for i in range(0, len(addl), 16):
            hash_block(addl[i:i+16])
        for i in range(0, len(data), 16):
            Ji += 1
            chunk = data[i:i+16]   # can't use xor_bytes below because chunk may be < 16 bytes
            newchunk = bytes(map(xor, chunk, self.aes.encrypt(iv + int_to_bytes(Ji, 4, 'big'))))
            data[i:i+16] = newchunk
            hash_block(chunk if decrypt else newchunk)
        hash_block((len(addl) << 67 | len(data) << 3).to_bytes(16, 'big'))
        auth_tag = (int_from_bytes(self.aes.encrypt(iv + b'\0\0\0\1'), 'big') ^
                    hash_state).to_bytes(16, 'big')
        return bytes(data), auth_tag

############################################################
### SHA1 / SHA256 / SHA512
############################################################

def primes_iter():
    yield from (2, 3)
    primes = [3]
    n = 5
    while True:
        for p in primes:
            if p * p > n:
                primes.append(n)
                yield n
                break
            elif n % p == 0:
                break
        n += 2

def floor_root(n, root):
    a, b = 0, n
    while True:
        m = (a + b) >> 1
        em = m ** root
        if em == n:      return m
        elif b - a == 1: return a
        elif em < n:     a = m   # too small
        else:            b = m   # too big

def sha2_constants(root, bits, n):
    return [floor_root(p << (bits * root), root) & ~(-1 << bits)
            for _, p in zip(range(n), primes_iter())]

class SHAx(object):

    def __init__(self, msg=b''):
        self.block_buffer = bytearray()
        self.processed_len = 0
        self.hash_state = self.initial_state
        self.update(msg)

    def update(self, msg):
        self.processed_len += len(msg)
        bb = self.block_buffer
        bb.extend(msg)
        bsz = self.block_size
        while len(bb) >= bsz:
            self.hash_state = self._process_block(consume_front(bb, bsz), self.hash_state)
        return self

    def digest(self):
        num_bits = self.processed_len * 8
        len_size = self.word_size * 2
        state = self.hash_state
        bb = self.block_buffer + b'\x80'
        bsz = self.block_size
        rem = bsz - len(bb)
        if rem >= len_size:
            bb += bytes(rem - len_size)
        else:
            bb += bytes(rem)
            state = self._process_block(bb, state)
            bb = bytearray(bsz - len_size)
        bb += num_bits.to_bytes(len_size, 'big')
        state = self._process_block(bb, state)
        return b''.join(x.to_bytes(self.word_size, 'big')
                        for x in state[:self.output_size // self.word_size])

    def copy(self):
        cls = type(self)
        new = cls.__new__(cls)
        new.block_buffer = self.block_buffer.copy()
        new.processed_len = self.processed_len
        new.hash_state = self.hash_state
        return new

    def _process_block(self, blk, state):
        assert len(blk) == self.block_size
        ws, nr = self.word_size, self.num_rounds
        sch = [int.from_bytes(blk[s:s+ws], 'big') for s in range(0, len(blk), ws)]
        while len(sch) < nr:
            sch.append(self._next_schedword(sch))
        blk_state = state
        for i, w in enumerate(sch):
            blk_state = self._run_round(blk_state, i, w)
        msk = (1 << (self.word_size * 8)) - 1
        return [(a + b) & msk for a, b in zip(state, blk_state)]

    def _next_schedword(self, sch): raise NotImplementedError
    def _run_round(self, state): raise NotImplementedError

class SHA1(SHAx):

    block_size  = 64
    word_size   = 4
    output_size = 20
    num_rounds  = 80
    initial_state = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

    f_20 = (
        lambda x, y, z: (x & y) ^ (~x & z),
        lambda x, y, z: x ^ y ^ z,
        lambda x, y, z: (x & y) ^ (x & z) ^ (y & z),
        lambda x, y, z: x ^ y ^ z,
    )
    k_20 = (0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6)

    def _next_schedword(self, sch):
        return rotl32(sch[-3] ^ sch[-8] ^ sch[-14] ^ sch[-16], 1)

    def _run_round(self, state, i, w):
        a, b, c, d, e = state
        T = (rotl32(a, 5) +
             self.f_20[i // 20](b, c, d) +
             e + self.k_20[i // 20] + w) & 0xFFFFFFFF
        return T, a, rotl32(b, 30), c, d

class SHA2(SHAx):

    Ch  = staticmethod(lambda x, y, z: (x & y) ^ (~x & z))
    Maj = staticmethod(lambda x, y, z: (x & y) ^ (x & z) ^ (y & z))

    def _next_schedword(self, sch):
        return (self.sigma1(sch[-2]) +
                sch[-7] +
                self.sigma0(sch[-15]) +
                sch[-16]) & self.word_mask

    def _run_round(self, state, i, w):
        a, b, c, d, e, f, g, h = state
        T1 = h + self.Sigma1(e) + self.Ch(e,f,g) + self.K[i] + w
        T2 = self.Sigma0(a) + self.Maj(a,b,c)
        msk = self.word_mask
        return (T1 + T2) & msk, a, b, c, (d + T1) & msk, e, f, g

class SHA256(SHA2):

    block_size  = 64
    word_size   = 4
    output_size = 32
    num_rounds  = 64
    initial_state = sha2_constants(2, 32, 8)
    word_mask = 0xFFFFFFFF

    Sigma0 = staticmethod(lambda x: rotr32(x,  2) ^ rotr32(x, 13) ^ rotr32(x, 22))
    Sigma1 = staticmethod(lambda x: rotr32(x,  6) ^ rotr32(x, 11) ^ rotr32(x, 25))
    sigma0 = staticmethod(lambda x: rotr32(x,  7) ^ rotr32(x, 18) ^ (x >> 3))
    sigma1 = staticmethod(lambda x: rotr32(x, 17) ^ rotr32(x, 19) ^ (x >> 10))

    K = sha2_constants(3, 32, num_rounds)

class SHA384(SHA2):

    block_size  = 128
    word_size   = 8
    output_size = 48
    num_rounds  = 80
    initial_state = sha2_constants(2, 64, 16)[8:]
    word_mask = 0xFFFFFFFFFFFFFFFF

    Ch  = staticmethod(lambda x, y, z: (x & y) ^ (~x & z))
    Maj = staticmethod(lambda x, y, z: (x & y) ^ (x & z) ^ (y & z))

    Sigma0 = staticmethod(lambda x: rotr64(x, 28) ^ rotr64(x, 34) ^ rotr64(x, 39))
    Sigma1 = staticmethod(lambda x: rotr64(x, 14) ^ rotr64(x, 18) ^ rotr64(x, 41))
    sigma0 = staticmethod(lambda x: rotr64(x,  1) ^ rotr64(x,  8) ^ (x >> 7))
    sigma1 = staticmethod(lambda x: rotr64(x, 19) ^ rotr64(x, 61) ^ (x >> 6))

    K = sha2_constants(3, 64, num_rounds)

############################################################
### HMAC
############################################################

class HMAC(object):
    def __init__(self, key, msg=b'', digestmod=None):
        bsz = digestmod.block_size
        if len(key) > bsz:
            key = digestmod(key).digest()
        if len(key) < bsz:
            key = key.ljust(bsz, b'\0')
        self.inner = digestmod(xor_bytes(key, b'\x36' * bsz))
        self.outer = digestmod(xor_bytes(key, b'\x5C' * bsz))
        self.inner.update(msg)
    def update(self, msg):
        self.inner.update(msg)
        return self
    def digest(self):
        outer = self.outer.copy()
        outer.update(self.inner.digest())
        return outer.digest()
    def copy(self):
        cls = type(self)
        new = cls.__new__(cls)
        new.inner = self.inner.copy()
        new.outer = self.outer.copy()
        return new

############################################################
### Elliptic Curves
############################################################

class ECCurve(object):
    def __init__(self, p, a, b, n, gx, gy):
        self.p, self.a, self.b, self.n = p, a, b, n
        self.octets = min_bytes_for_int(p)
        self.g = ECPoint(gx, gy, self)
    def inv(self, x):
        p = self.p
        t, nt = 0, 1
        r, nr = p, x % p
        while nr:
            q = r // nr
            t, nt = nt, t - q * nt
            r, nr = nr, r - q * nr
        t %= p
        assert (t * x) % p == 1
        return t

class ECPoint(object):
    def __init__(self, x, y, curve):
        c = self.curve = curve
        self.x, self.y = x % c.p, y % c.p
        if (x or y) and (x ** 2 - (y ** 3 + c.a * x + c.b)) % c.p == 0:
            raise ValueError('point not on curve')
    def __bool__(self):
        return bool(self.x or self.y)
    def __add__(a, b):
        c = a.curve
        if a.curve is not b.curve: raise ValueError('curve mismatch')
        if not a: return b
        if not b: return a
        x1, y1, x2, y2 = a.x, a.y, b.x, b.y
        if x1 == x2 and (y1 + y2) % c.p == 0: return ECPoint(0, 0, c)
        if x1 == x2 and y1 == y2: return a * 2
        l = ((y2 - y1) * c.inv(x2 - x1)) % c.p
        x3 = l * l - x1 - x2
        y3 = l * (x1 - x3) - y1
        return ECPoint(x3, y3, c)
    def __mul__(p, s):
        c = p.curve
        if not p: return ECPoint(0, 0, c)
        if s == 2:
            x1, y1 = p.x, p.y
            l = ((3 * x1 * x1 + c.a) * c.inv(2 * y1)) % c.p
            x3 = l * l - 2 * x1
            y3 = l * (x1 - x3) - y1
            return ECPoint(x3, y3, c)
        else:
            r = ECPoint(0, 0, c)
            while s:
                if s & 1: r += p
                p, s = p * 2, s >> 1
            return r
    def __bytes__(self):
        c = self.curve
        return b''.join((b'\4',
                         self.x.to_bytes(c.octets, 'big'),
                         self.y.to_bytes(c.octets, 'big')))
    @staticmethod
    def from_bytes(data, curve):
        if data and data[0] != 4: raise ValueError('uncompressed only')
        if len(data) != 1 + 2 * curve.octets: raise ValueError('wrong size')
        x = int.from_bytes(data[1:1+curve.octets], 'big')
        y = int.from_bytes(data[1+curve.octets:], 'big')
        return ECPoint(x, y, curve)

############################################################
### RSA
############################################################

class RSAPublicKey(object):
    def __init__(self, m, e):
        self.m, self.e = m, e
        self.size = min_bytes_for_int(m)
    def encrypt(self, data):
        b = b''.join((b'\0\2', urandom_nonzero(self.size - len(data) - 3), b'\0', data))
        return pow(int.from_bytes(b, 'big'), self.e, self.m).to_bytes(self.size, 'big')
    def verify(self, data, signature, expected_hash_algo):
        if len(signature) != self.size: raise ValueError('wrong size')
        x = pow(int.from_bytes(signature, 'big'), self.e, self.m)
        b = x.to_bytes(self.size, 'big')
        if b[:2] != b'\0\1': raise ValueError('bad signature')
        b = b[2:].lstrip(b'\xFF')
        if b[0] != 0: raise ValueError('bad signature')
        (sig_algo, _), sig_hash = parse_asn1(b[1:], single=True)
        if (X509_HASH_ALGOS[sig_algo.value] is not expected_hash_algo or
                sig_hash.value != expected_hash_algo(data).digest()):
            raise ValueError('bad signature')

############################################################
### ASN.1
############################################################

class ASN1BitString(object):
    def __init__(self, content_bytes, unused_bits):
        self.content_bytes, self.unused_bits = content_bytes, unused_bits
        if not 0 <= unused_bits <= 7: raise ValueError('invalid number of unused bits')
        if content_bytes[-1] & ((1 << unused_bits) - 1): raise ValueError('unused bits not zero')
    def __bytes__(self):
        if self.unused_bits != 0: raise ValueError('not even octets')
        return self.content_bytes
    def __int__(self):
        cb, nb = self.content_bytes, len(self.content_bytes) * 8
        n = int.from_bytes(cb, 'big')
        return int('{:0{}b}'.format(n, nb)[::-1], 2)   # reverse bit order

class ASN1Node(object):
    RAW_TO_VALUE = {
        1:  lambda raw: bool(raw[0]) if len(raw) == 1 else int(''),  # Boolean
        2:  lambda raw: int.from_bytes(raw, 'big', signed=True),     # Integer
        3:  lambda raw: ASN1BitString(bytes(raw[1:]), raw[0]),       # BitString
        4:  lambda raw: bytes(raw),                                  # OctetString
        5:  lambda raw: None if raw == b'' else int(''),             # Null
        6:  lambda raw: __class__.__parse_oid(bytes(raw)),           # OID
        12: lambda raw: str(raw, 'utf-8'),                           # UTF8String
        18: lambda raw: str(raw, 'ascii'),                           # NumericString
        19: lambda raw: str(raw, 'ascii'),                           # PrintableString
        20: lambda raw: str(raw, 'ascii'),                           # TeletexString
        21: lambda raw: str(raw, 'ascii'),                           # VideotexString
        22: lambda raw: str(raw, 'ascii'),                           # IA5String
        23: lambda raw: __class__.__parse_time(str(raw, 'ascii')),   # UTCTime
        24: lambda raw: __class__.__parse_time(str(raw, 'ascii')),   # GeneralizedTime
        28: lambda raw: str(raw, 'utf-8'),                           # UniversalString
    }
    def __init__(self, klass, constructed, tag, raw):
        self.klass, self.constructed, self.tag = klass, constructed, tag
        self.raw, self.value = raw, None
    def __getitem__(self, index):
        return self.value[index]
    def __len__(self):
        return len(self.value)
    def __iter__(self):
        return iter(self.value)
    def __repr__(self):
        if self.klass:
            return '<{}/{}: {}>'.format(self.klass, self.tag, repr(self.value))
        return '<{}>'.format(repr(self.value))
    def __parse_time(raw):
        for fmt in ('%y%m%d%H%M%SZ', '%Y%m%d%H%M%SZ'):
            try:
                return datetime.strptime(raw, fmt)
            except ValueError:
                pass
        raise ValueError('invalid time string: {}'.format(raw))
    def __parse_oid(raw):
        cur, subs = None, []
        for x in raw:
            cur = (cur or 0) << 7 | (x & 0x7F)
            if not (x & 0x80):
                subs.append(cur)
                cur = None
        if cur is not None: raise ValueError('unfinished OID')
        x, y = 2, subs[0] - 80
        while y < 0: x, y = x - 1, y + 40
        subs[0:1] = [x, y]
        return '.'.join(str(x) for x in subs)

def parse_asn1(data, *, single=False, decoder=None):
    if type(data) is not memoryview: data = memoryview(data)
    nodes = []
    while data:
        klass, constructed, tag = data[0] >> 6, data[0] >> 5 & 0x1, data[0] & 0x1F
        if tag == 0x1F: raise NotImplementedError('multi-byte ident unsupported')
        length = data[1]
        length_length = 0
        if length == 0xFF: raise NotImplementedError('indefinite length unsupported')
        if length & 0x80: 
            length_length = length & 0x7F
            length_bytes = data[2:2+length_length]
            if len(length_bytes) != length_length: raise ValueError('unexpected end of length')
            length = int.from_bytes(length_bytes, 'big')
        header, data = partition_data(data, 2 + length_length)
        raw, data = partition_data(data, length)
        node = ASN1Node(klass, constructed, tag, bytes(header) + bytes(raw))
        nodes.append(node)
        if constructed:
            node.value = parse_asn1(raw, decoder=decoder)
        elif klass != 0x0 and decoder:
            node.value = decoder(klass, tag, raw)
        else:
            node.value = ASN1Node.RAW_TO_VALUE[tag](raw)
    if single:
        [nodes] = nodes
    return nodes

def asn1_find_child_with_tag(node, cls, tag):
    return next((x for x in node if x.klass == cls and x.tag == tag), None)

def asn1_get_node_for_pair_key(node, key_value, unwrap_levels=0):
    for _ in range(unwrap_levels): node = (x for [x] in node)
    node = list(node)
    return next((v for k, *v in node if k.value == key_value), None)

############################################################
### X.509
############################################################

X509_HASH_ALGOS = {
    '2.16.840.1.101.3.4.2.1': SHA256,
    '2.16.840.1.101.3.4.2.2': SHA384,
    '1.3.14.3.2.26': SHA1,
}

X509_RSA_HASH_ALGOS = {
    '1.2.840.113549.1.1.11': SHA256,
    '1.2.840.113549.1.1.12': SHA384,
    '1.2.840.113549.1.1.5':  SHA1,
}

def x509_san_decoder(klass, tag, raw):
    if klass != 2 or tag != 2: raise ValueError('only DNS SAN supported')
    return str(raw, 'ascii')

class X509Cert(object):
    def __init__(self, tree):
        'tree is result from parse_asn1(data, single=True)'
        self.tree = tree
        if not (tree[0][0].klass == 0x2 and
                tree[0][0].tag == 0 and
                tree[0][0][0].value == 2):
            # not a v3 cert
            tree[0].value.insert(0, None)
        if tree[0][2].raw != tree[1].raw:
            raise ValueError('cert has algo mismatch')
    def get_extension_data(self, oid):
        cert_ext = only_or_none(asn1_find_child_with_tag(self.tree[0], 0x2, 3))
        if cert_ext is None: return None
        ext_data_nodes = asn1_get_node_for_pair_key(cert_ext, oid)
        return ext_data_nodes[-1].value if ext_data_nodes is not None else None
    def get_subject_bytes(self):
        return self.tree[0][5].raw
    def get_issuer_bytes(self):
        return self.tree[0][3].raw
    def has_rsa_key(self):
        (algo, _), _ = self.tree[0][6]
        return algo.value == '1.2.840.113549.1.1.1'
    def extract_rsa_key(self):
        if not self.has_rsa_key(): raise NotImplementedError('non-RSA key')
        pk_m, pk_e = parse_asn1(bytes(self.tree[0][6][1].value), single=True)
        return RSAPublicKey(pk_m.value, pk_e.value)
    def verify_validity_period(self, now_dt):
        valid_start, valid_end = self.tree[0][4]
        valid_start, valid_end = valid_start.value, valid_end.value
        if not valid_start <= now_dt <= valid_end:
            raise ValueError('cert has expired or used too early')
    def extract_common_name(self):
        cn_node = only_or_none(asn1_get_node_for_pair_key(self.tree[0][5], '2.5.4.3', 1))
        return cn_node.value if cn_node is not None else None
    def extract_subj_alt_names(self):
        san_ext_data = self.get_extension_data('2.5.29.17')
        if san_ext_data is None: return []
        san_ext = parse_asn1(san_ext_data, single=True, decoder=x509_san_decoder)
        return [n.value for n in san_ext]
    def verify_desired_key_usage(self, desired_key_usage):
        key_usg_data = self.get_extension_data('2.5.29.15')
        if key_usg_data is not None:
            key_usg_bit_str = parse_asn1(key_usg_data, single=True)
            key_usg = int(key_usg_bit_str.value)
            if (key_usg & desired_key_usage) != desired_key_usage:
                raise ValueError('key used for wrong purpose')
    def verify_is_cert_authority(self, cert_idx):
        basic_constraints_data = self.get_extension_data('2.5.29.19')
        if basic_constraints_data is None: raise ValueError('no basic constraints found')
        basic_constraints = parse_asn1(basic_constraints_data, single=True)
        if not (len(basic_constraints) > 0 and
                type(basic_constraints[0].value) is bool and
                basic_constraints[0].value):
            raise ValueError('non-CA cert used as CA')
        maybe_path_len = basic_constraints[-1].value
        if type(maybe_path_len) is int and cert_idx - 1 > maybe_path_len:
            raise ValueError('cert chain too long')
    def verify_cert_against_issuer(self, issuer):
        if self.get_issuer_bytes() != issuer.get_subject_bytes():
            raise ValueError('invalid cert chain')
        algo, _ = self.tree[1]
        expected_hash_algo = X509_RSA_HASH_ALGOS[algo.value]
        issuer.extract_rsa_key().verify(self.tree[0].raw,
                                        bytes(self.tree[2].value),
                                        expected_hash_algo)

class X509CertStore(object):
    __DEFAULT = None
    def __init__(self, filename):
        self.store = store = {}
        with open(filename, 'rb') as fd:
            lines = [x.rstrip() for x in fd]
        begin_lines = [i for i, x in enumerate(lines) if x == b'-----BEGIN CERTIFICATE-----']
        end_lines = [i for i, x in enumerate(lines) if x == b'-----END CERTIFICATE-----']
        if (len(begin_lines) != len(end_lines) or
                not all(a < b for a, b in zip(begin_lines, end_lines))):
            raise ValueError('badly formed cert bundle')
        for begin, end in zip(begin_lines, end_lines):
            cert_b64 = b''.join(lines[begin+1:end])
            cert_data = base64_decode(cert_b64)
            cert = X509Cert(parse_asn1(cert_data, single=True))
            if cert.has_rsa_key():
                cert.extract_common_name()  # test that this works
                cert.extract_rsa_key()      # test that this works
                store[cert.get_subject_bytes()] = cert
    def is_issuer_of_cert_in_store(self, cert):
        return cert.get_issuer_bytes() in self.store
    def verify_cert_against_store(self, cert):
        ca = self.store.get(cert.get_issuer_bytes(), None)
        if ca is None: raise ValueError('issuer not in store')
        cert.verify_cert_against_issuer(ca)
        return ca
    @classmethod
    def get_default(cls):
        if cls.__DEFAULT is None:
            cls.__DEFAULT = X509CertStore('ca_certs.pem')
        return cls.__DEFAULT

############################################################
### TLS encryption
############################################################

class TLSBlockCipher(object):
    def __init__(self, enc_key, enc_iv, enc_algo, mac_key, hash_algo, enc_then_mac):
        self.enc_cipher = enc_algo(enc_key)
        self.init_hmac = HMAC(mac_key, b'', hash_algo)
        self.enc_blk_size = enc_algo.block_size
        self.mac_out_size = hash_algo.output_size
        self.enc_then_mac = enc_then_mac
    def encrypt(self, header, fragment):
        if self.enc_then_mac:
            return self._enc_addmac(header, self._enc_encrypt(fragment))
        else:
            return self._enc_encrypt(self._enc_addmac(header, fragment))
    def decrypt(self, header, fragment):
        if self.enc_then_mac:
            return self._dec_decrypt(self._dec_checkmac(header, fragment))
        else:
            return self._dec_checkmac(header, self._dec_decrypt(fragment))
    def _enc_encrypt(self, fragment):
        fragment, ebsz = bytearray(fragment), self.enc_blk_size
        pad_len = ebsz - len(fragment) % ebsz       # padding must be non-empty
        fragment += bytes((pad_len - 1,)) * pad_len # mandated by standard
        iv = last = urandom(ebsz)
        for i in range(0, len(fragment), ebsz):
            fragment[i:i+ebsz] = last = self.enc_cipher.encrypt(xor_bytes(last, fragment[i:i+ebsz]))
        return iv + fragment
    def _enc_addmac(self, header, fragment):
        header.length = len(fragment)
        return bytes(fragment) + self.init_hmac.copy().update(bytes(header)).update(fragment).digest()
    def _dec_checkmac(self, header, fragment):
        fragment, given_mac = partition_data(fragment, -self.mac_out_size)
        header.length = len(fragment)
        expected_mac = self.init_hmac.copy().update(bytes(header)).update(fragment).digest()
        if given_mac != expected_mac: raise ValueError('bad MAC')
        return fragment
    def _dec_decrypt(self, fragment):
        ebsz = self.enc_blk_size
        if len(fragment) % ebsz: raise ValueError('fragment not multiple of block size')
        iv, fragment = partition_data(fragment, ebsz)
        if not fragment: raise ValueError('empty fragment')
        fragment = bytearray(fragment)
        for i in range(0, len(fragment), ebsz):
            inp = fragment[i:i+ebsz]
            iv, fragment[i:i+ebsz] = inp, xor_bytes(iv, self.enc_cipher.decrypt(inp))
        pad_len = fragment[-1] + 1
        if fragment[-pad_len:] != bytes((pad_len - 1,)) * pad_len: raise ValueError('padding error')
        del fragment[-pad_len:]
        return bytes(fragment)

class TLSAEADCipher(object):
    def __init__(self, enc_key, enc_iv, enc_algo, mac_key, hash_algo, enc_then_mac):
        self.enc_cipher = enc_algo(enc_key, enc_iv)
        self.nonce_size = enc_algo.nonce_size
        self.tag_size   = enc_algo.tag_size
        assert not enc_then_mac
    def encrypt(self, header, fragment):
        header.length = len(fragment)
        nonce = header.seq_num.to_bytes(self.nonce_size, 'big')
        return nonce + self.enc_cipher.encrypt(nonce, bytes(header), fragment)
    def decrypt(self, header, fragment):
        nsz, tsz = self.nonce_size, self.tag_size
        nonce, fragment = partition_data(fragment, nsz)
        header.length = len(fragment) - tsz
        return self.enc_cipher.decrypt(nonce, bytes(header), fragment)

############################################################
### TLS key exchange
############################################################

TLS_HASH_ALGOS = { 2: SHA1, 4: SHA256, 5: SHA384 }

class RSA(object):
    requires_server_key_exchange = False
    # pre_master_secret set by build_client_key_exchange
    def build_client_key_exchange(self, pub_key):
        pms_struct = TLSStructures.PreMasterSecret(client_version=TLS_VERSION_INT,
                                                   random=urandom(46))
        pms = self.pre_master_secret = bytes(pms_struct)
        client_key_exchange = TLSStructures.ClientKeyExchangeRSA(
            enc_pre_master_secret=pub_key.encrypt(pms))
        return bytes(client_key_exchange)

class DHE(object):
    requires_server_key_exchange = True
    # pre_master_secret set by build_client_key_exchange
    def _skx_common(self, pub_key, cs_randoms, skx, struct_class):
        skx_struct = struct_class.decode_structure_from_bytes(skx)
        if skx_struct.sig_algo != 1: raise ValueError('only rsa supported')
        pub_key.verify(cs_randoms + bytes(skx_struct.params),
                       skx_struct.signature,
                       TLS_HASH_ALGOS[skx_struct.hash_algo])
        return skx_struct
    def _gen_rand(self, max_num):
        nbl = max_num.bit_length()
        while True:
            d = int.from_bytes(urandom((nbl + 7) // 8), 'big')
            d = d & ((1 << nbl) - 1) | 1 << (nbl - 1)
            if d < max_num: return d
    def process_server_key_exchange(self, pub_key, cs_randoms, skx):
        skx_struct = self._skx_common(pub_key, cs_randoms, skx, TLSStructures.ServerKeyExchangeDHE)
        self.dh_p  = int.from_bytes(skx_struct.params.dh_p,  'big')
        self.dh_g  = int.from_bytes(skx_struct.params.dh_g,  'big')
        self.dh_Ys = int.from_bytes(skx_struct.params.dh_Ys, 'big')
    def build_client_key_exchange(self, pub_key):
        dh_c = self._gen_rand(self.dh_p)
        dh_Yc = pow(self.dh_g,  dh_c, self.dh_p)
        dh_z  = pow(self.dh_Ys, dh_c, self.dh_p)
        pms = dh_z.to_bytes(min_bytes_for_int(dh_z), 'big')
        self.pre_master_secret = pms
        client_key_exchange = TLSStructures.ClientKeyExchangeDHE(
            dh_Yc=dh_Yc.to_bytes(min_bytes_for_int(dh_Yc), 'big'))
        return bytes(client_key_exchange)

ECDHE_NAMED_CURVES = {
    23: ECCurve(p  = (1 << 256) - (1 << 224) + (1 << 192) + (1 << 96) - 1,
                a  = (1 << 256) - (1 << 224) + (1 << 192) + (1 << 96) - 4,
                b  = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B,
                n  = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
                gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
                gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5),
}

class ECDHE(DHE):
    requires_server_key_exchange = True
    # pre_master_secret set by build_client_key_exchange
    def process_server_key_exchange(self, pub_key, cs_randoms, skx):
        skx_struct = self._skx_common(pub_key, cs_randoms, skx, TLSStructures.ServerKeyExchangeECDHE)
        if skx_struct.params.curve_type != 3: raise NotImplementedError('only named curves supported')
        self.curve = ECDHE_NAMED_CURVES[skx_struct.params.namedcurve]
        self.server = ECPoint.from_bytes(skx_struct.params.public, self.curve)
    def build_client_key_exchange(self, pub_key):
        d = self._gen_rand(self.curve.n)
        secret = self.server * d
        client = self.curve.g * d
        self.pre_master_secret = secret.x.to_bytes(self.curve.octets, 'big')
        client_key_exchange = TLSStructures.ClientKeyExchangeECDHE(
            ecdh_Yc=bytes(client))
        return bytes(client_key_exchange)

############################################################
### TLS cipher suites
############################################################

class TLSCipherSuite(object):
    def __init__(self, enc_algo, key_size, cipher_class, kex_algo, hash_algo=None, prf_algo=SHA256):
        self.enc_algo     = enc_algo
        self.key_size     = key_size
        self.cipher_class = cipher_class
        self.kex_algo     = kex_algo
        self.hash_algo    = hash_algo
        self.prf_algo     = prf_algo
        self.mac_size     = hash_algo.output_size if hash_algo else 0
        self.iv_size      = enc_algo.iv_size if cipher_class is TLSAEADCipher else 0
    def PRF(self, secret, label, seed, length):
        A = seed = label + seed
        result = bytearray()
        while len(result) < length:
            A = HMAC(secret, A, self.prf_algo).digest()
            result += HMAC(secret, A + seed, self.prf_algo).digest()
        return bytes(result[:length])
    def __repr__(self):
        cls_name = lambda x: x.__name__ if x is not None else 'None'
        return '{}(enc_algo={}, key_size={}, cipher_class={}, kex_algo={}, hash_algo={}, prf_algo={})'.format(
            cls_name(self.__class__), cls_name(self.enc_algo), self.key_size, cls_name(self.cipher_class),
            cls_name(self.kex_algo), cls_name(self.hash_algo), cls_name(self.prf_algo))


# aRSA:!eNULL:-SRP:-PSK:-AESCCM:-AESCCM8:-CAMELLIA:-CHACHA20:-SEED:-IDEA
TLS_CIPHER_SUITES = {
    0x002F: TLSCipherSuite(enc_algo=AES,    key_size=16, cipher_class=TLSBlockCipher, kex_algo=RSA, hash_algo=SHA1),
    0x0033: TLSCipherSuite(enc_algo=AES,    key_size=16, cipher_class=TLSBlockCipher, kex_algo=DHE, hash_algo=SHA1),
    0x0035: TLSCipherSuite(enc_algo=AES,    key_size=32, cipher_class=TLSBlockCipher, kex_algo=RSA, hash_algo=SHA1),
    0x0039: TLSCipherSuite(enc_algo=AES,    key_size=32, cipher_class=TLSBlockCipher, kex_algo=DHE, hash_algo=SHA1),
    0x003C: TLSCipherSuite(enc_algo=AES,    key_size=16, cipher_class=TLSBlockCipher, kex_algo=RSA, hash_algo=SHA256),
    0x003D: TLSCipherSuite(enc_algo=AES,    key_size=32, cipher_class=TLSBlockCipher, kex_algo=RSA, hash_algo=SHA256),
    0x0067: TLSCipherSuite(enc_algo=AES,    key_size=16, cipher_class=TLSBlockCipher, kex_algo=DHE, hash_algo=SHA256),
    0x006B: TLSCipherSuite(enc_algo=AES,    key_size=32, cipher_class=TLSBlockCipher, kex_algo=DHE, hash_algo=SHA256),
    0x009C: TLSCipherSuite(enc_algo=AESGCM, key_size=16, cipher_class=TLSAEADCipher,  kex_algo=RSA),
    0x009D: TLSCipherSuite(enc_algo=AESGCM, key_size=32, cipher_class=TLSAEADCipher,  kex_algo=RSA, prf_algo=SHA384),
    0x009E: TLSCipherSuite(enc_algo=AESGCM, key_size=16, cipher_class=TLSAEADCipher,  kex_algo=DHE),
    0x009F: TLSCipherSuite(enc_algo=AESGCM, key_size=32, cipher_class=TLSAEADCipher,  kex_algo=DHE, prf_algo=SHA384),
    0xC013: TLSCipherSuite(enc_algo=AES,    key_size=16, cipher_class=TLSBlockCipher, kex_algo=ECDHE, hash_algo=SHA1),
    0xC014: TLSCipherSuite(enc_algo=AES,    key_size=32, cipher_class=TLSBlockCipher, kex_algo=ECDHE, hash_algo=SHA1),
    0xC027: TLSCipherSuite(enc_algo=AES,    key_size=16, cipher_class=TLSBlockCipher, kex_algo=ECDHE, hash_algo=SHA256),
    0xC028: TLSCipherSuite(enc_algo=AES,    key_size=32, cipher_class=TLSBlockCipher, kex_algo=ECDHE, hash_algo=SHA384, prf_algo=SHA384),
    0xC02F: TLSCipherSuite(enc_algo=AESGCM, key_size=16, cipher_class=TLSAEADCipher,  kex_algo=ECDHE),
    0xC030: TLSCipherSuite(enc_algo=AESGCM, key_size=32, cipher_class=TLSAEADCipher,  kex_algo=ECDHE, prf_algo=SHA384),
}

# sort ciphersuites by order of preference
TLS_CIPHER_SUITE_ID_LIST = [id for id, cs in sorted(TLS_CIPHER_SUITES.items(),
                                                    key=lambda it: ((AESGCM, AES).index(it[1].enc_algo),
                                                                    (ECDHE, DHE, RSA).index(it[1].kex_algo),
                                                                    (SHA384, SHA256, SHA1, None).index(it[1].hash_algo)))]

############################################################
### TLS main
############################################################

TLS_VERSION_INT = 0x0303

TLS_CONTENT_CHANGECIPHERSPEC = 20
TLS_CONTENT_ALERT            = 21
TLS_CONTENT_HANDSHAKE        = 22
TLS_CONTENT_APPLICATIONDATA  = 23

TLS_HANDSHAKE_CLIENTHELLO       = 1
TLS_HANDSHAKE_SERVERHELLO       = 2
TLS_HANDSHAKE_CERTIFICATE       = 11
TLS_HANDSHAKE_SERVERKEYEXCHANGE = 12
TLS_HANDSHAKE_SERVERHELLODONE   = 14
TLS_HANDSHAKE_CLIENTKEYEXCHANGE = 16
TLS_HANDSHAKE_FINISHED          = 20

class TLSFatalAlert(IOError):
    def __init__(self, level, description):
        super().__init__('level {} desc {}'.format(level, description))
        self.level, self.description = level, description

class TLSConnectionState(object):
    def __init__(self, mac, key, iv, cipher_suite, enc_then_mac):
        self.seq = 0
        self.cipher = cipher_suite.cipher_class(
            key, iv, cipher_suite.enc_algo, mac, cipher_suite.hash_algo, enc_then_mac)
    def encrypt(self, type, version, fragment):
        header = TLSStructures.MACCalculationHeader(
            seq_num=self.seq, type=type, version=version, length=0) # length filled later
        self.seq += 1
        return self.cipher.encrypt(header, fragment)
    def decrypt(self, type, version, fragment):
        header = TLSStructures.MACCalculationHeader(
            seq_num=self.seq, type=type, version=version, length=0) # length filled later
        self.seq += 1
        return self.cipher.decrypt(header, fragment)

class TLSConnection(object):

    def __init__(self, sock, hostname, cipher_suites=None, verify_certs=True):
        self.fd = sock.makefile('rwb')
        self.hostname = hostname
        self.readbuf = bytearray()
        self.eof = False
        self.cipher_suites = cipher_suites or TLS_CIPHER_SUITE_ID_LIST
        self.verify_certs = verify_certs
        self.pending_write_state, self.active_write_state = None, None
        self.pending_read_state,  self.active_read_state  = None, None

    def do_handshake(self):
        self._start_handshake()
        while self.handshake is not None:
            self._process_record()

    def recv(self, n):
        if not self.eof:
            try:
                while not self.readbuf:
                    self._process_record()
            except EOFError:
                self.eof = True
        return bytes(consume_front(self.readbuf, n))

    def send(self, data):
        self._send_records(TLS_CONTENT_APPLICATIONDATA, data)
        return len(data)

    def _read_fully(self, size):
        data = self.fd.read(size)
        if len(data) != size:
            raise EOFError('socket closed')
        return data

    def _process_record(self):
        self.fd.flush()
        record = TLSStructures.TLSRecord.decode_structure_from_stream(self._read_fully)
        if self.active_read_state is not None:
            data = self.active_read_state.decrypt(record.type, record.protocol_version, record.fragment)
        else:
            data = record.fragment
        if record.type == TLS_CONTENT_APPLICATIONDATA:
            self.readbuf += data
        elif record.type == TLS_CONTENT_HANDSHAKE: # handshake packet
            try:
                self.handshake.send(data) # send data to coroutine
            except StopIteration as e:
                if e.value == 'handshake_complete':
                    self.handshake = None
                else:
                    raise
        elif record.type == TLS_CONTENT_CHANGECIPHERSPEC:
            assert self.pending_read_state is not None
            self.active_read_state, self.pending_read_state = self.pending_read_state, None
        elif record.type == TLS_CONTENT_ALERT:
            level, description = data
            if description == 0: # close notify
                self.eof = True
            elif level == 1: # warning
                print('ssl warning ({})'.format(description), file=stderr)
            else: # fatal
                raise TLSFatalAlert(level, description)
        else:
            raise ValueError('unknown content type {}'.format(record.type))
    
    def _start_handshake(self):
        self.handshake = self._handshake_coro()
        self.handshake.send(None) # start the coroutine and send ClientHello

    def _send_records(self, type, data):
        mv = memoryview(data)
        for i in range(0, len(mv), TLS_RECORD_MAX_SIZE):
            fragment = mv[i:i+TLS_RECORD_MAX_SIZE]
            if self.active_write_state is not None:
                fragment = self.active_write_state.encrypt(type, TLS_VERSION_INT, fragment)
            self.fd.write(bytes(TLSStructures.TLSRecord(
                type=type,
                protocol_version=TLS_VERSION_INT,
                fragment=fragment)))

    def _send_ccs(self):
        self._send_records(TLS_CONTENT_CHANGECIPHERSPEC, b'\1')
        assert self.pending_write_state is not None
        self.active_write_state, self.pending_write_state = self.pending_write_state, None

    def _handshake_coro(self):
        incoming_buffer = bytearray()
        handshake_hash = bytearray()   # changes to digestmod object later

        def rec_read(n):
            'coroutine: reads n bytes of handshake content data'
            while len(incoming_buffer) < n:
                incoming_buffer.extend((yield))
            return bytes(consume_front(incoming_buffer, n))

        def handshake_add_to_hash(data):
            hh = handshake_hash
            (hh.extend if type(hh) is bytearray else hh.update)(data)

        def send_handshake_msg(type, data):
            handshake_msg = bytes((type,)) + len(data).to_bytes(3, 'big') + data 
            handshake_add_to_hash(handshake_msg)
            self._send_records(TLS_CONTENT_HANDSHAKE, handshake_msg)

        def recv_handshake_msg(expected_type):
            header = yield from rec_read(4)
            type = header[0]
            length = int.from_bytes(header[1:4], 'big')
            if type != expected_type:
                raise ValueError('expected type {} but got {}'.format(expected_type, type))
            data = yield from rec_read(length)
            handshake_add_to_hash(header)
            handshake_add_to_hash(data)
            return data

        self.server_hello_done = False

        # ClientHello
        sig_algos = [0x0201, 0x0401, 0x0501] # SHA1/SHA256/SHA384 with RSA
        hello_extensions = [
            TLSStructures.HelloExtension(
                extension_type=0x0000,
                extension_data=bytes(TLSStructures.ServerNameIndication(server_name_list=[
                    TLSStructures.ServerName(name_type=0, host_name=self.hostname.encode('ascii'))]))),
            TLSStructures.HelloExtension(
                extension_type=0x000D,
                extension_data=bytes(TLSStructures.SupportedSignatureAlgorithms(algos=sig_algos))),
            TLSStructures.HelloExtension(
                extension_type=0x0016, extension_data=b'')
        ]
        if any(TLS_CIPHER_SUITES[id].kex_algo is ECDHE for id in self.cipher_suites):
            supported_curves_ints = [len(ECDHE_NAMED_CURVES) * 2] + list(ECDHE_NAMED_CURVES.keys())
            hello_extensions += [
                TLSStructures.HelloExtension(
                    extension_type=0x000B,
                    extension_data=bytes((1, 0))), # uncompressed point format
                TLSStructures.HelloExtension(
                    extension_type=0x000A,
                    extension_data=b''.join(x.to_bytes(2, 'big') for x in supported_curves_ints))]
        client_hello = TLSStructures.ClientHello(
            client_version=TLS_VERSION_INT,
            random=urandom(32),
            session_id=b'',
            cipher_suites=self.cipher_suites,
            compression_methods=[0],
            extensions=hello_extensions)
        send_handshake_msg(TLS_HANDSHAKE_CLIENTHELLO, bytes(client_hello))

        # ServerHello
        server_hello = TLSStructures.ServerHello.decode_structure_from_bytes(
            (yield from recv_handshake_msg(TLS_HANDSHAKE_SERVERHELLO)))
        cipher_suite = TLS_CIPHER_SUITES[server_hello.cipher_suite]
        enc_then_mac = any(he.extension_type == 0x0016 for he in server_hello.extensions)

        print('chosen cipher suite:', repr(cipher_suite), file=stderr)
        self.server_hello_done = True

        # setup handshake hash and PRF
        handshake_hash = cipher_suite.prf_algo(handshake_hash)
        PRF = cipher_suite.PRF
        kex = cipher_suite.kex_algo()

        # Certificate
        certificate = TLSStructures.Certificate.decode_structure_from_bytes(
            (yield from recv_handshake_msg(TLS_HANDSHAKE_CERTIFICATE)))
        prev_cert, prev_cert_raw = None, None
        skipped_certs = 0
        if self.verify_certs:
            current_time = datetime.utcnow()
            cert_store = X509CertStore.get_default()
        for cert_idx, cert_raw in enumerate(certificate.certificate_list):
            if cert_raw == prev_cert_raw: # broken impls duplicate certs in chain
                skipped_certs += 1
                continue
            cert = X509Cert(parse_asn1(cert_raw, single=True))
            if prev_cert is None:
                pub_key = cert.extract_rsa_key()
                if not self.verify_certs:
                    break
                cert.verify_validity_period(current_time)
                cert.verify_desired_key_usage(1 << 2 if isinstance(kex, RSA) else 1 << 0)
                hostname_patterns = list(cert.extract_subj_alt_names())
                common_name = cert.extract_common_name()
                common_name and hostname_patterns.append(common_name)
                if not any(host_match(self.hostname, p) for p in hostname_patterns):
                    raise ValueError('wrong hostname')
            else: # rest of certs in chain
                cert.verify_desired_key_usage(1 << 5)
                cert.verify_is_cert_authority(cert_idx - skipped_certs)
                prev_cert.verify_cert_against_issuer(cert)
            prev_cert, prev_cert_raw = cert, cert_raw
            if cert_store.is_issuer_of_cert_in_store(cert):
                ca_cert = cert_store.verify_cert_against_store(cert)
                print('trusted via:', ca_cert.extract_common_name(), file=stderr)
                break
        else:
            raise ValueError('untrusted cert chain')

        # ServerKeyExchange
        if kex.requires_server_key_exchange:
            kex.process_server_key_exchange(pub_key, client_hello.random + server_hello.random,
                (yield from recv_handshake_msg(TLS_HANDSHAKE_SERVERKEYEXCHANGE)))

        # ServerHelloDone
        server_hello_done = yield from recv_handshake_msg(TLS_HANDSHAKE_SERVERHELLODONE)
        assert server_hello_done == b''

        # ClientKeyExchange
        client_key_exchange_bytes = kex.build_client_key_exchange(pub_key)
        send_handshake_msg(TLS_HANDSHAKE_CLIENTKEYEXCHANGE,
                           client_key_exchange_bytes)

        # setup pending connection state
        key_block_components = (cipher_suite.mac_size, cipher_suite.key_size, cipher_suite.iv_size)
        master_secret = PRF(kex.pre_master_secret, b'master secret',
                            client_hello.random + server_hello.random, 48)
        key_block = PRF(master_secret, b'key expansion',
                        server_hello.random + client_hello.random, 2 * sum(key_block_components))
        key_block_read = create_reader(key_block)
        keys = [key_block_read(sz) for sz in key_block_components for _ in (1, 2)]
        self.pending_write_state = TLSConnectionState(mac=keys[0], key=keys[2], iv=keys[4],
                                                      cipher_suite=cipher_suite, enc_then_mac=enc_then_mac)
        self.pending_read_state  = TLSConnectionState(mac=keys[1], key=keys[3], iv=keys[5],
                                                      cipher_suite=cipher_suite, enc_then_mac=enc_then_mac)

        # ChangeCipherSpec
        self._send_ccs()

        # Client Finished
        verify_data = PRF(master_secret, b'client finished', handshake_hash.digest(), 12)
        client_finished = TLSStructures.Finished(verify_data=verify_data)
        send_handshake_msg(TLS_HANDSHAKE_FINISHED, bytes(client_finished))

        # Server Finished
        expected_verify_data = PRF(master_secret, b'server finished', handshake_hash.digest(), 12)
        server_finished = TLSStructures.Finished.decode_structure_from_bytes(
            (yield from recv_handshake_msg(TLS_HANDSHAKE_FINISHED)))
        if server_finished.verify_data != expected_verify_data:
            raise ValueError('bad finished message')

        return 'handshake_complete'

def run_connection(url, handle, verify_certs=True, cipher_suites=None):
    hostname, httppath = split_url(url)
    with socket() as sock:
        sock.connect((hostname, 443))
        tls = TLSConnection(sock, hostname, verify_certs=verify_certs, cipher_suites=cipher_suites)
        try:
            tls.do_handshake()
        except TLSFatalAlert as exc:
            if exc.description == 40:
                return False
            raise
        except ConnectionResetError:
            return False
        tls.send('GET {} HTTP/1.1\r\nHost: {}\r\nConnection: close\r\n\r\n'.format(httppath, hostname).encode())
        while True:
            b = tls.recv(65536)
            if not b:
                break
            handle(b)
    return True

def run_fetch_mode(url, opts):
    if not run_connection(url, stdout.buffer.write, verify_certs='no-cert-check' not in opts):
        raise Exception('all ciphers unsupported for host')

def run_test_mode(url, opts):
    def handle(b):
        out_buf.extend(b)
    for cipher_suite in TLS_CIPHER_SUITE_ID_LIST:
        print('testing 0x{:04x} ...'.format(cipher_suite))
        out_buf = bytearray()
        run_ok = run_connection(url, handle, verify_certs='no-cert-check' not in opts, cipher_suites=[cipher_suite])
        if not run_ok:
            print('unsupported!')
        elif b'HTTP/1' not in out_buf:
            print('bad response!')
        else:
            print('OK!')
        print()

def usage():
    print('Usage: {} [--test] [--no-cert-check] https://...'.format(argv[0]), file=stderr)
    raise SystemExit(1)

def main():
    if len(argv) == 1:
        return usage()
    url, opts = None, set()
    for arg in argv[1:]:
        if arg in ('-h', '--help'):
            return usage()
        elif arg.startswith('--'):
            opts.add(arg[2:])
        elif url is not None:
            raise ValueError('only single URL accepted')
        else:
            url = arg
    bad_opts = opts - {'test', 'no-cert-check'}
    if bad_opts:
        raise ValueError('unrecognized options: {!r}'.format(bad_opts))
    if 'test' in opts:
        run_test_mode(url, opts)
    else:
        run_fetch_mode(url, opts)

if __name__ == '__main__':
    main()
