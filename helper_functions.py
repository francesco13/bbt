#%pip install eth_keys
#%pip install qrcode
#%pip install pycryptodome
#%pip install bitcoinaddress 
from __future__ import annotations

import qrcode
import base64
import logging
import math
import struct

from IPython.display import SVG, display
from qrcode.image.svg import SvgImage
from eth_keys import keys 

from Crypto.Hash import keccak, SHA256, SHA512
from Crypto.Util.number import isPrime
from Crypto.Cipher import PKCS1_OAEP
from Crypto.PublicKey import RSA
from Crypto.Random import get_random_bytes
#from bitcoinaddress import Wallet

logger = logging.getLogger(__name__)

_KEY_BITS = 2048 
_PRIME_BITS  = _KEY_BITS // 2
_PUBLIC_EXP  = 65537

SEPOLIA_CHAIN_ID = 11155111

_KECCAK_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]

_KECCAK_ROT = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]

_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
_Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
_Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
_G = (_Gx, _Gy)


def _rot64(x, n):
    return ((x << n) | (x >> (64 - n))) & 0xFFFFFFFFFFFFFFFF


def _keccak_f(state):
    for rc in _KECCAK_RC:
        C = [state[x][0] ^ state[x][1] ^ state[x][2] ^ state[x][3] ^ state[x][4] for x in range(5)]
        D = [C[(x - 1) % 5] ^ _rot64(C[(x + 1) % 5], 1) for x in range(5)]
        state = [[state[x][y] ^ D[x] for y in range(5)] for x in range(5)]

        B = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                B[y][(2 * x + 3 * y) % 5] = _rot64(state[x][y], _KECCAK_ROT[x][y])

        state = [[B[x][y] ^ ((~B[(x + 1) % 5][y]) & B[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
        state[0][0] ^= rc
    return state


def _keccak256(data):
    rate_bytes = 136
    msg = bytearray(data)
    msg.append(0x01)
    while len(msg) % rate_bytes:
        msg.append(0x00)
    msg[-1] |= 0x80

    state = [[0] * 5 for _ in range(5)]
    for i in range(0, len(msg), rate_bytes):
        words = struct.unpack_from("<17Q", msg, i)
        idx = 0
        for y in range(5):
            for x in range(5):
                if idx < 17:
                    state[x][y] ^= words[idx]
                    idx += 1
        state = _keccak_f(state)

    out = b""
    for y in range(5):
        for x in range(5):
            out += struct.pack("<Q", state[x][y])
            if len(out) >= 32:
                return out[:32]
    return out[:32]


def _rlp_len(n, offset):
    if n < 56:
        return bytes([offset + n])
    nb = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([offset + 55 + len(nb)]) + nb


def _rlp_bytes(b):
    if len(b) == 1 and b[0] < 0x80:
        return b
    return _rlp_len(len(b), 0x80) + b


def _rlp_int(n):
    raw = b"" if n == 0 else n.to_bytes((n.bit_length() + 7) // 8, "big")
    return _rlp_bytes(raw)


def _rlp_list(items):
    body = b"".join(items)
    return _rlp_len(len(body), 0xC0) + body


def _rlp_decode_length(data, offset):
    prefix = data[offset]
    if prefix < 0x80:
        return offset, 1, "str"
    elif prefix <= 0xB7:
        return offset + 1, prefix - 0x80, "str"
    elif prefix <= 0xBF:
        ll = prefix - 0xB7
        return offset + 1 + ll, int.from_bytes(data[offset + 1: offset + 1 + ll], "big"), "str"
    elif prefix <= 0xF7:
        return offset + 1, prefix - 0xC0, "list"
    else:
        ll = prefix - 0xF7
        return offset + 1 + ll, int.from_bytes(data[offset + 1: offset + 1 + ll], "big"), "list"


def _rlp_decode_list(data):
    data_offset, length, _ = _rlp_decode_length(data, 0)
    body = data[data_offset: data_offset + length]
    items = []
    cursor = 0
    while cursor < len(body):
        item_offset, item_len, _ = _rlp_decode_length(body, cursor)
        items.append(body[cursor: item_offset + item_len])
        cursor = item_offset + item_len
    return items


def _point_add(P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2:
        return _point_double(P) if y1 == y2 else None
    lam = ((y2 - y1) * pow(x2 - x1, _P - 2, _P)) % _P
    x3 = (lam * lam - x1 - x2) % _P
    return x3, (lam * (x1 - x3) - y1) % _P


def _point_double(P):
    if P is None:
        return None
    x1, y1 = P
    lam = (3 * x1 * x1 * pow(2 * y1, _P - 2, _P)) % _P
    x3 = (lam * lam - 2 * x1) % _P
    return x3, (lam * (x1 - x3) - y1) % _P


def _scalar_mult(k, P):
    R, Q = None, P
    while k:
        if k & 1:
            R = _point_add(R, Q)
        Q = _point_double(Q)
        k >>= 1
    return R


def _ecdsa_sign(msg_hash, priv):
    k = int.from_bytes(_keccak256(priv.to_bytes(32, "big") + msg_hash), "big") % _N
    k = k or 1
    pt = _scalar_mult(k, _G)
    r = pt[0] % _N
    s = pow(k, _N - 2, _N) * (int.from_bytes(msg_hash, "big") + r * priv) % _N
    if s > _N // 2:
        s = _N - s
    v = 0 if pt[1] % 2 == 0 else 1
    return v, r, s


def serialise(
    nonce,
    to,
    value_wei,
    max_fee_per_gas,
    max_priority_fee_per_gas,
    gas_limit=21_000,
    data=b"",
    chain_id=SEPOLIA_CHAIN_ID,
):
    to_hex = to.strip().lower().removeprefix("0x")
    if len(to_hex) != 40:
        raise ValueError(f"'to' must be a 20-byte Ethereum address, got: {to!r}")
    to_bytes = bytes.fromhex(to_hex)

    payload = b"\x02" + _rlp_list([
        _rlp_int(chain_id),
        _rlp_int(nonce),
        _rlp_int(max_priority_fee_per_gas),
        _rlp_int(max_fee_per_gas),
        _rlp_int(gas_limit),
        _rlp_bytes(to_bytes),
        _rlp_int(value_wei),
        _rlp_bytes(data),
        _rlp_list([]),
    ])

    logger.debug(
        "serialise: chain=%d nonce=%d to=0x%s value=%d gas=%d payload=%d B",
        chain_id, nonce, to_hex, value_wei, gas_limit, len(payload),
    )
    return payload


def sign(payload, private_key_hex):
    if not isinstance(payload, (bytes, bytearray)):
        raise TypeError(f"payload must be bytes, got {type(payload).__name__!r}")
    if not isinstance(private_key_hex, str):
        raise TypeError(f"private_key_hex must be str, got {type(private_key_hex).__name__!r}")

    raw_hex = private_key_hex.strip().removeprefix("0x")
    if len(raw_hex) != 64:
        raise ValueError(f"private_key_hex must be 64 hex characters (32 bytes), got {len(raw_hex)}")

    priv = int(raw_hex, 16)
    if not (1 <= priv < _N):
        raise ValueError("Private key is out of the valid secp256k1 range.")

    msg_hash = _keccak256(payload)
    logger.debug("sign: msg_hash=0x%s", msg_hash.hex())
    v, r, s = _ecdsa_sign(msg_hash, priv)
    logger.debug("sign: v=%d  r=0x%064x  s=0x%064x", v, r, s)

    fields = _rlp_decode_list(payload[1:])
    signed = b"\x02" + _rlp_list(fields + [
        _rlp_int(v),
        _rlp_bytes(r.to_bytes(32, "big")),
        _rlp_bytes(s.to_bytes(32, "big")),
    ])
    logger.debug("sign: raw_tx=%d bytes", len(signed))
    return signed

def sign_message(message: str, private_key_hex: str) -> dict:
    private_key = keys.PrivateKey(bytes.fromhex(private_key_hex.removeprefix("0x")))
    msg_hash = _keccak256(message.encode("utf-8"))
    signature = private_key.sign_msg_hash(msg_hash)

    return signature.to_bytes().hex()


def verify_signature(message: str, signature_hex: str) -> bool:
    msg_hash = _keccak256(message.encode("utf-8"))
    signature = keys.Signature(bytes.fromhex(signature_hex.removeprefix("0x")))
    recovered_key = signature.recover_public_key_from_msg_hash(msg_hash)
    return recovered_key


def display_qr(data: str):
    factory = SvgImage
    img = qrcode.make(data, image_factory=factory)
    display(SVG(img.to_string()))

def xy64_to_sec_keys(raw_xy_hex: str, ):
    """
    Convert a 64-byte raw X||Y public key (128 hex chars) into:
      - compressed SEC public key
      - uncompressed SEC public key

    Returns: (compressed_hex, uncompressed_hex)
    """
    h = raw_xy_hex.lower().strip()
    if h.startswith("0x"):
        h = h[2:]

    if len(h) != 128:
        raise ValueError("expected 64 bytes of raw X/Y coordinates (128 hex chars)")

    x_hex = h[:64]
    y_hex = h[64:]

    y = int(y_hex, 16)
    prefix = "02" if y % 2 == 0 else "03"

    compressed = prefix + x_hex
    uncompressed = "04" + x_hex + y_hex
    return compressed, uncompressed

def ec_key_from_decimal(decimal_number: int):
    private_key_hex = hex(decimal_number)[2:].zfill(64)
    private_key = keys.PrivateKey(bytes.fromhex(private_key_hex))
    public_key = private_key.public_key
    public_key_compressed, public_key_uncompressed = xy64_to_sec_keys(public_key.to_hex())
    
    # Derive Ethereum address
    ethereum_address = public_key.to_checksum_address()

    # Derive P2TR bitcoin address
    Bitcoin_bc1_P2TR = p2tr_address_from_pubkey(public_key_compressed, testnet=False)
    Bitcoin_tb1_P2TR = p2tr_address_from_pubkey(public_key_compressed, testnet=True)
    
    return {
        "decimal": decimal_number,
        "private_key_hex": "0x" + private_key_hex,
        "public_key_compressed": public_key_compressed,
        "public_key_uncompressed": public_key_uncompressed,
        "ethereum_address": ethereum_address,
        "bitcoin_bc1_P2TR": Bitcoin_bc1_P2TR,
        "bitcoin_tb1_P2TR": Bitcoin_tb1_P2TR,        
    }
###
def _seed_to_bytes(seed: int) -> bytes:
    """Encode a (possibly very large) integer as a big-endian byte string."""
    length = max(1, (seed.bit_length() + 7) // 8)
    return seed.to_bytes(length, "big")


def _derive_prime(seed_bytes: bytes, label: str) -> int:
    """Deterministically derive a 1024-bit prime from *seed_bytes*.

    Strategy
    --------
    1. Hash  seed || label  with SHA-512 to get a 512-bit digest.
    2. Concatenate two such digests (different counters) → 1024 bits.
    3. Force the top two bits to 1 (ensures the number is 1024 bits
       and odd) and the bottom bit to 1 (odd → candidate for prime).
    4. Walk upward (+2 each step) until a prime is found.
    """
    candidates: list[bytes] = []
    counter = 0
    while len(candidates) < 2:
        h = SHA512.new()
        h.update(seed_bytes)
        h.update(label.encode())
        h.update(counter.to_bytes(4, "big"))
        candidates.append(h.digest())   # 64 bytes each
        counter += 1

    raw   = candidates[0] + candidates[1]          # 128 bytes = 1024 bits
    n     = int.from_bytes(raw, "big")

    # Force to exactly _PRIME_BITS bits, odd
    n    |= (1 << (_PRIME_BITS - 1)) | (1 << (_PRIME_BITS - 2))
    n    |= 1                                       # must be odd

    # Walk to the next prime
    while not isPrime(n):
        n += 2

    logger.debug("_derive_prime(%s): found %d-bit prime", label, n.bit_length())
    return n


def _mod_inv(a: int, m: int) -> int:
    """Extended-Euclidean modular inverse of *a* mod *m*."""
    g, x, _ = _extended_gcd(a, m)
    if g != 1:
        raise ValueError(f"No modular inverse: gcd({a}, {m}) = {g}")
    return x % m


def _extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    if a == 0:
        return b, 0, 1
    g, x, y = _extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

import hashlib

def p2tr_address_from_pubkey(pubkey_hex, testnet=False):
    P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    G = (
        55066263022277343669578718895168534326250603453777594175500187360389116729240,
        32670510020758816978083085130507043184471273380659243275938904335757337482424,
    )
    CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
    BECH32M_CONST = 0x2BC830A3

    def inv(a): return pow(a, -1, P)

    def add(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A
        x2, y2 = B
        if x1 == x2 and (y1 + y2) % P == 0:
            return None
        if A == B:
            m = (3 * x1 * x1) * inv((2 * y1) % P) % P
        else:
            m = (y2 - y1) * inv((x2 - x1) % P) % P
        x3 = (m * m - x1 - x2) % P
        y3 = (m * (x1 - x3) - y1) % P
        return (x3, y3)

    def mul(k, A):
        R = None
        while k:
            if k & 1:
                R = add(R, A)
            A = add(A, A)
            k >>= 1
        return R

    def tagged_hash(tag, msg):
        t = hashlib.sha256(tag.encode()).digest()
        return hashlib.sha256(t + t + msg).digest()

    def decode_pubkey(sec):
        sec = bytes.fromhex(sec)
        if len(sec) != 33 or sec[0] not in (2, 3):
            raise ValueError("expected compressed public key hex")
        x = int.from_bytes(sec[1:], "big")
        y = pow((pow(x, 3, P) + 7) % P, (P + 1) // 4, P)
        if (y & 1) != (sec[0] & 1):
            y = P - y
        return (x, y)

    def polymod(vals):
        g = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
        chk = 1
        for v in vals:
            b = chk >> 25
            chk = ((chk & 0x1FFFFFF) << 5) ^ v
            for i in range(5):
                if (b >> i) & 1:
                    chk ^= g[i]
        return chk

    def hrp_expand(hrp):
        return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]

    def convertbits(data, frombits, tobits):
        acc = bits = 0
        out = []
        maxv = (1 << tobits) - 1
        for b in data:
            acc = (acc << frombits) | b
            bits += frombits
            while bits >= tobits:
                bits -= tobits
                out.append((acc >> bits) & maxv)
        if bits:
            out.append((acc << (tobits - bits)) & maxv)
        return out

    def bech32m_encode(hrp, data):
        vals = hrp_expand(hrp) + data
        pm = polymod(vals + [0, 0, 0, 0, 0, 0]) ^ BECH32M_CONST
        checksum = [(pm >> 5 * (5 - i)) & 31 for i in range(6)]
        return hrp + "1" + "".join(CHARSET[d] for d in data + checksum)

    P_int = decode_pubkey(pubkey_hex)
    if P_int[1] & 1:
        P_int = (P_int[0], P - P_int[1])  # x-only internal key must have even y

    xonly = P_int[0].to_bytes(32, "big")
    tweak = int.from_bytes(tagged_hash("TapTweak", xonly), "big") % N
    Q = add(P_int, mul(tweak, G))
    if Q is None:
        raise ValueError("invalid tweaked key")

    witness_program = Q[0].to_bytes(32, "big")
    return bech32m_encode("tb" if testnet else "bc", [1] + convertbits(witness_program, 8, 5))

    

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def rsa_key_from_decimal(decimal_number: int) -> tuple[RSA.RsaKey, RSA.RsaKey]:

    if not isinstance(decimal_number, int):
        raise TypeError(
            f"decimal_number must be int, got {type(decimal_number).__name__!r}"
        )
    if decimal_number < 1:
        raise ValueError(f"decimal_number must be a positive integer, got {decimal_number}")

    seed_bytes = _seed_to_bytes(decimal_number)

    # ── Derive two distinct 1024-bit primes ────────────────────────────────
    p = _derive_prime(seed_bytes, "p")
    q = _derive_prime(seed_bytes, "q")

    # Ensure p ≠ q  (astronomically unlikely but guard anyway)
    if p == q:
        q = _derive_prime(seed_bytes, "q2")

    # ── RSA key construction ───────────────────────────────────────────────
    n   = p * q
    lcm = (p - 1) * (q - 1) // math.gcd(p - 1, q - 1)   # λ(n)
    e   = _PUBLIC_EXP
    d   = _mod_inv(e, lcm)

    private_key = RSA.construct((n, e, d, p, q))
    public_key  = private_key.publickey()

    logger.debug(
        "keypair_from_decimal(%d…): n=%d bits",
        decimal_number % 10_000,          # log only last 4 digits
        n.bit_length(),
    )
    return {
        "decimal": decimal_number,
        "private_key": private_key,
        "public_key": public_key
     }


def encrypt(plaintext: str, public_key: RSA.RsaKey) -> str:
    """Encrypt *plaintext* with *public_key* using RSA-OAEP / SHA-256.

    Parameters
    ----------
    plaintext : str
        UTF-8 message to encrypt.
        Maximum ~190 bytes for a 2048-bit key.
    public_key : RSA.RsaKey
        RSA public key returned by :func:`keypair_from_decimal`.

    Returns
    -------
    str
        URL-safe base64-encoded ciphertext.

    Raises
    ------
    TypeError
        If *plaintext* is not ``str`` or *public_key* is not ``RSA.RsaKey``.

    Examples
    --------
    >>> priv, pub = keypair_from_decimal(99999)
    >>> token = encrypt("Hello!", pub)
    >>> isinstance(token, str)
    True
    """
    if not isinstance(plaintext, str):
        raise TypeError(f"plaintext must be str, got {type(plaintext).__name__!r}")
    if not isinstance(public_key, RSA.RsaKey):
        raise TypeError(f"public_key must be RSA.RsaKey, got {type(public_key).__name__!r}")

    cipher     = PKCS1_OAEP.new(public_key, hashAlgo=SHA256)
    ciphertext = cipher.encrypt(plaintext.encode("utf-8"))
    token      = base64.urlsafe_b64encode(ciphertext).decode("ascii")

    logger.debug("encrypt: %d B → %d char token", len(plaintext), len(token))
    return token


def decrypt(token: str, private_key: RSA.RsaKey) -> str:
    """Decrypt a token produced by :func:`encrypt`.

    Parameters
    ----------
    token : str
        Base64-url-safe string returned by :func:`encrypt`.
    private_key : RSA.RsaKey
        RSA private key from :func:`keypair_from_decimal`.

    Returns
    -------
    str
        The original UTF-8 plaintext.

    Raises
    ------
    TypeError
        If *token* is not ``str`` or *private_key* is not ``RSA.RsaKey``.
    ValueError
        If the token is malformed, the key is wrong, or decryption fails.

    Examples
    --------
    >>> priv, pub = keypair_from_decimal(99999)
    >>> token     = encrypt("Hello!", pub)
    >>> decrypt(token, priv)
    'Hello!'
    """
    if not isinstance(token, str):
        raise TypeError(f"token must be str, got {type(token).__name__!r}")
    if not isinstance(private_key, RSA.RsaKey):
        raise TypeError(f"private_key must be RSA.RsaKey, got {type(private_key).__name__!r}")
    if not private_key.has_private():
        raise ValueError("private_key must contain the private key component.")

    try:
        ciphertext = base64.urlsafe_b64decode(token.encode("ascii"))
    except Exception as exc:
        raise ValueError(f"Invalid base64 token: {exc}") from exc

    try:
        cipher          = PKCS1_OAEP.new(private_key, hashAlgo=SHA256)
        plaintext_bytes = cipher.decrypt(ciphertext)
    except (ValueError, TypeError) as exc:
        raise ValueError("Decryption failed — wrong key or corrupted token.") from exc

    plaintext = plaintext_bytes.decode("utf-8")
    logger.debug("decrypt: %d B ciphertext → %d B plaintext", len(ciphertext), len(plaintext))
    return plaintext



