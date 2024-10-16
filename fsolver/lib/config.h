// arithmetic
static size_t ARITH_MAX = 35;

// interesting values
#define INTERESTING_8 \
    0x80, /* Overflow signed 8-bit when decremented: -128 */ \
    0xff, /* -1 */ \
    0, /* 0 */ \
    1, /* 1 */ \
    16, /* One-off with common buffer size */ \
    32, /* One-off with common buffer size, space */ \
    64, /* One-off with common buffer size */ \
    100, /* One-off with common buffer size */ \
    127, /* Overflow signed 8-bit when incremented */\
    10, /* LF */\
    13, /* CR */\
    48, /* '0' */\
    53, /* '5' */\
    57, /* '9' */\
    65, /* 'A' */\
    70, /* 'F' */\
    80, /* 'P' */\
    90, /* 'Z' */\
    97, /* 'a' */\
    102, /* 'f' */\
    112, /* 'p' */\
    122 /* 'z' */

#define INTERESTING_16 \
    0x8000, /* Overflow signed 16-bit when decremented: -32768 */ \
    0xFF7F, /* Overflow signed 8-bit: -129 */ \
    128, /* Overflow signed 8-bit */ \
    255, /* Overflow unsig 8-bit when incremented */ \
    256, /* Overflow unsig 8-bit */ \
    512, /* One-off with common buffer size */ \
    1000, /* One-off with common buffer size */ \
    1024, /* One-off with common buffer size */ \
    4096, /* One-off with common buffer size */ \
    32767 /* Overflow signed 16-bit when incremented */

#define INTERESTING_32 \
    0x80000000, /* Overflow signed 32-bit when decremented */ \
    0xFA0000FA, /* Large negative number (endian-agnostic) */ \
    0xFFFF7FFF, /* Overflow signed 16-bit: -32769 */ \
    32768, /* Overflow signed 16-bit */ \
    65535, /* Overflow unsig 16-bit when incremented */ \
    65536, /* Overflow unsig 16 bit */ \
    100663045, /* Large positive number (endian-agnostic) */ \
    2147483647 /* Overflow signed 32-bit when incremented */

#define INTERESTING_32_FLOAT \
    0x0, /* +0.0 */ \
    0x80000000, /* -0.0 */ \
    0x3f800000, /* +1.0 */ \
    0x40000000, /* +2.0 */ \
    0xbf800000, /* -1.0 */ \
    0xc0000000, /* -2.0 */ \
    0x7f7fffff, /* +3.4028234663852886e+38 */ \
    0xff7fffff, /* -3.4028234663852886e+38 */ \
    0x7f800000, /* +inf */ \
    0x7fc00000, /* +nan */ \
    0xff800000, /* -inf */ \
    0xffc00000, /* -nan */ \
    0x1, /* subnormal */ \
    0x80000001, /* -subnormal */ \
    0x10, /* subnormal */ \
    0x80000010 /* -subnormal */

#define INTERESTING_64 \
    0x8000000000000000LL, /* Overflow signed 64-bit when decremented */ \
    0xf00000000000000fLL,/* Large negative number: 0xf00000000000000f */ \
    0x80000000LL, /* Overflow signed 32-bit: -2147483648 */ \
    2147483647LL, /* Overflow signed 32-bit */ \
    4294967295LL, /* Overflow unsig 32-bit when incremented */ \
    4294967296LL, /* Overflow unsig 32-bit */ \
    4611686018427388000LL, /* Large positive number: 0x4000000000000004 */ \
    9223372036854775807LL /* Overflow signed 64-bit when incremented */

#define INTERESTING_64_FLOAT \
    0x0, /* +0.0 */ \
    0x8000000000000000, /* -0.0 */ \
    0x3ff0000000000000, /* +1.0 */ \
    0x4000000000000000, /* +2.0 */ \
    0xbff0000000000000, /* -1.0 */ \
    0xc000000000000000, /* -2.0 */ \
    0x7fefffffffffffff, /* +1.7976931348623157e+308 */ \
    0xffefffffffffffff, /* -1.7976931348623157e+308 */ \
    0x7ff0000000000000, /* +inf */ \
    0x7ff8000000000000, /* +nan */ \
    0xfff0000000000000, /* -inf */ \
    0xfff8000000000000, /* -nan */ \
    0x1, /* subnormal */ \
    0x8000000000000001, /* -subnormal */ \
    0x10, /* subnormal */ \
    0x8000000000000010 /* -subnormal */

static uint8_t interesting_8[]  = { INTERESTING_8 };
static uint16_t interesting_16[] = { INTERESTING_8, INTERESTING_16 };
static uint32_t interesting_32[] = { INTERESTING_8, INTERESTING_16, INTERESTING_32, INTERESTING_32_FLOAT };
static uint64_t interesting_64[] = { INTERESTING_8, INTERESTING_16, INTERESTING_32, INTERESTING_32_FLOAT, INTERESTING_64, INTERESTING_64_FLOAT };
static size_t interesting_8_len = sizeof(interesting_8) / sizeof(int8_t);
static size_t interesting_16_len = sizeof(interesting_16) / sizeof(int16_t);
static size_t interesting_32_len = sizeof(interesting_32) / sizeof(int32_t);
static size_t interesting_64_len = sizeof(interesting_64) / sizeof(int64_t);

// type aware interesting values
static uint8_t interesting_8_bitvector[] = { INTERESTING_8 };
static uint16_t interesting_16_bitvector[] = { INTERESTING_8, INTERESTING_16 };
static uint32_t interesting_32_bitvector[] = { INTERESTING_8, INTERESTING_16, INTERESTING_32 };
static uint64_t interesting_64_bitvector[] = { INTERESTING_8, INTERESTING_16, INTERESTING_32, INTERESTING_64 };
static size_t interesting_8_bitvector_len = sizeof(interesting_8_bitvector) / sizeof(int8_t);
static size_t interesting_16_bitvector_len = sizeof(interesting_16_bitvector) / sizeof(int16_t);
static size_t interesting_32_bitvector_len = sizeof(interesting_32_bitvector) / sizeof(int32_t);
static size_t interesting_64_bitvector_len = sizeof(interesting_64_bitvector) / sizeof(int64_t);
static uint32_t interesting_32_float[] = { INTERESTING_32_FLOAT };
static uint64_t interesting_64_float[] = { INTERESTING_64_FLOAT };
static size_t interesting_32_float_len = sizeof(interesting_32_float) / sizeof(int32_t);
static size_t interesting_64_float_len = sizeof(interesting_64_float) / sizeof(int64_t);

// havoc
#define HAVOC_TIMES 20

// splice
#define SPLICE_TIMES 10
