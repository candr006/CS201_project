/*===- TableGen'erated file -------------------------------------*- C++ -*-===*\
|*                                                                            *|
|*Target Instruction Enum Values                                              *|
|*                                                                            *|
|* Automatically generated file, do not edit!                                 *|
|*                                                                            *|
\*===----------------------------------------------------------------------===*/


#ifdef GET_INSTRINFO_ENUM
#undef GET_INSTRINFO_ENUM
namespace llvm {

namespace XCore {
  enum {
    PHI	= 0,
    INLINEASM	= 1,
    CFI_INSTRUCTION	= 2,
    EH_LABEL	= 3,
    GC_LABEL	= 4,
    KILL	= 5,
    EXTRACT_SUBREG	= 6,
    INSERT_SUBREG	= 7,
    IMPLICIT_DEF	= 8,
    SUBREG_TO_REG	= 9,
    COPY_TO_REGCLASS	= 10,
    DBG_VALUE	= 11,
    REG_SEQUENCE	= 12,
    COPY	= 13,
    BUNDLE	= 14,
    LIFETIME_START	= 15,
    LIFETIME_END	= 16,
    STACKMAP	= 17,
    PATCHPOINT	= 18,
    LOAD_STACK_GUARD	= 19,
    STATEPOINT	= 20,
    FRAME_ALLOC	= 21,
    ADD_2rus	= 22,
    ADD_3r	= 23,
    ADJCALLSTACKDOWN	= 24,
    ADJCALLSTACKUP	= 25,
    ANDNOT_2r	= 26,
    AND_3r	= 27,
    ASHR_l2rus	= 28,
    ASHR_l3r	= 29,
    BAU_1r	= 30,
    BITREV_l2r	= 31,
    BLACP_lu10	= 32,
    BLACP_u10	= 33,
    BLAT_lu6	= 34,
    BLAT_u6	= 35,
    BLA_1r	= 36,
    BLRB_lu10	= 37,
    BLRB_u10	= 38,
    BLRF_lu10	= 39,
    BLRF_u10	= 40,
    BRBF_lru6	= 41,
    BRBF_ru6	= 42,
    BRBT_lru6	= 43,
    BRBT_ru6	= 44,
    BRBU_lu6	= 45,
    BRBU_u6	= 46,
    BRFF_lru6	= 47,
    BRFF_ru6	= 48,
    BRFT_lru6	= 49,
    BRFT_ru6	= 50,
    BRFU_lu6	= 51,
    BRFU_u6	= 52,
    BRU_1r	= 53,
    BR_JT	= 54,
    BR_JT32	= 55,
    BYTEREV_l2r	= 56,
    CHKCT_2r	= 57,
    CHKCT_rus	= 58,
    CLRE_0R	= 59,
    CLRPT_1R	= 60,
    CLRSR_branch_lu6	= 61,
    CLRSR_branch_u6	= 62,
    CLRSR_lu6	= 63,
    CLRSR_u6	= 64,
    CLZ_l2r	= 65,
    CRC8_l4r	= 66,
    CRC_l3r	= 67,
    DCALL_0R	= 68,
    DENTSP_0R	= 69,
    DGETREG_1r	= 70,
    DIVS_l3r	= 71,
    DIVU_l3r	= 72,
    DRESTSP_0R	= 73,
    DRET_0R	= 74,
    ECALLF_1r	= 75,
    ECALLT_1r	= 76,
    EDU_1r	= 77,
    EEF_2r	= 78,
    EET_2r	= 79,
    EEU_1r	= 80,
    EH_RETURN	= 81,
    ENDIN_2r	= 82,
    ENTSP_lu6	= 83,
    ENTSP_u6	= 84,
    EQ_2rus	= 85,
    EQ_3r	= 86,
    EXTDP_lu6	= 87,
    EXTDP_u6	= 88,
    EXTSP_lu6	= 89,
    EXTSP_u6	= 90,
    FRAME_TO_ARGS_OFFSET	= 91,
    FREER_1r	= 92,
    FREET_0R	= 93,
    GETD_l2r	= 94,
    GETED_0R	= 95,
    GETET_0R	= 96,
    GETID_0R	= 97,
    GETKEP_0R	= 98,
    GETKSP_0R	= 99,
    GETN_l2r	= 100,
    GETPS_l2r	= 101,
    GETR_rus	= 102,
    GETSR_lu6	= 103,
    GETSR_u6	= 104,
    GETST_2r	= 105,
    GETTS_2r	= 106,
    INCT_2r	= 107,
    INITCP_2r	= 108,
    INITDP_2r	= 109,
    INITLR_l2r	= 110,
    INITPC_2r	= 111,
    INITSP_2r	= 112,
    INPW_l2rus	= 113,
    INSHR_2r	= 114,
    INT_2r	= 115,
    IN_2r	= 116,
    Int_MemBarrier	= 117,
    KCALL_1r	= 118,
    KCALL_lu6	= 119,
    KCALL_u6	= 120,
    KENTSP_lu6	= 121,
    KENTSP_u6	= 122,
    KRESTSP_lu6	= 123,
    KRESTSP_u6	= 124,
    KRET_0R	= 125,
    LADD_l5r	= 126,
    LD16S_3r	= 127,
    LD8U_3r	= 128,
    LDA16B_l3r	= 129,
    LDA16F_l3r	= 130,
    LDAPB_lu10	= 131,
    LDAPB_u10	= 132,
    LDAPF_lu10	= 133,
    LDAPF_lu10_ba	= 134,
    LDAPF_u10	= 135,
    LDAWB_l2rus	= 136,
    LDAWB_l3r	= 137,
    LDAWCP_lu6	= 138,
    LDAWCP_u6	= 139,
    LDAWDP_lru6	= 140,
    LDAWDP_ru6	= 141,
    LDAWFI	= 142,
    LDAWF_l2rus	= 143,
    LDAWF_l3r	= 144,
    LDAWSP_lru6	= 145,
    LDAWSP_ru6	= 146,
    LDC_lru6	= 147,
    LDC_ru6	= 148,
    LDET_0R	= 149,
    LDIVU_l5r	= 150,
    LDSED_0R	= 151,
    LDSPC_0R	= 152,
    LDSSR_0R	= 153,
    LDWCP_lru6	= 154,
    LDWCP_lu10	= 155,
    LDWCP_ru6	= 156,
    LDWCP_u10	= 157,
    LDWDP_lru6	= 158,
    LDWDP_ru6	= 159,
    LDWFI	= 160,
    LDWSP_lru6	= 161,
    LDWSP_ru6	= 162,
    LDW_2rus	= 163,
    LDW_3r	= 164,
    LMUL_l6r	= 165,
    LSS_3r	= 166,
    LSUB_l5r	= 167,
    LSU_3r	= 168,
    MACCS_l4r	= 169,
    MACCU_l4r	= 170,
    MJOIN_1r	= 171,
    MKMSK_2r	= 172,
    MKMSK_rus	= 173,
    MSYNC_1r	= 174,
    MUL_l3r	= 175,
    NEG	= 176,
    NOT	= 177,
    OR_3r	= 178,
    OUTCT_2r	= 179,
    OUTCT_rus	= 180,
    OUTPW_l2rus	= 181,
    OUTSHR_2r	= 182,
    OUTT_2r	= 183,
    OUT_2r	= 184,
    PEEK_2r	= 185,
    REMS_l3r	= 186,
    REMU_l3r	= 187,
    RETSP_lu6	= 188,
    RETSP_u6	= 189,
    SELECT_CC	= 190,
    SETCLK_l2r	= 191,
    SETCP_1r	= 192,
    SETC_l2r	= 193,
    SETC_lru6	= 194,
    SETC_ru6	= 195,
    SETDP_1r	= 196,
    SETD_2r	= 197,
    SETEV_1r	= 198,
    SETKEP_0R	= 199,
    SETN_l2r	= 200,
    SETPSC_2r	= 201,
    SETPS_l2r	= 202,
    SETPT_2r	= 203,
    SETRDY_l2r	= 204,
    SETSP_1r	= 205,
    SETSR_branch_lu6	= 206,
    SETSR_branch_u6	= 207,
    SETSR_lu6	= 208,
    SETSR_u6	= 209,
    SETTW_l2r	= 210,
    SETV_1r	= 211,
    SEXT_2r	= 212,
    SEXT_rus	= 213,
    SHL_2rus	= 214,
    SHL_3r	= 215,
    SHR_2rus	= 216,
    SHR_3r	= 217,
    SSYNC_0r	= 218,
    ST16_l3r	= 219,
    ST8_l3r	= 220,
    STET_0R	= 221,
    STSED_0R	= 222,
    STSPC_0R	= 223,
    STSSR_0R	= 224,
    STWDP_lru6	= 225,
    STWDP_ru6	= 226,
    STWFI	= 227,
    STWSP_lru6	= 228,
    STWSP_ru6	= 229,
    STW_2rus	= 230,
    STW_l3r	= 231,
    SUB_2rus	= 232,
    SUB_3r	= 233,
    SYNCR_1r	= 234,
    TESTCT_2r	= 235,
    TESTLCL_l2r	= 236,
    TESTWCT_2r	= 237,
    TSETMR_2r	= 238,
    TSETR_3r	= 239,
    TSTART_1R	= 240,
    WAITEF_1R	= 241,
    WAITET_1R	= 242,
    WAITEU_0R	= 243,
    XOR_l3r	= 244,
    ZEXT_2r	= 245,
    ZEXT_rus	= 246,
    INSTRUCTION_LIST_END = 247
  };

namespace Sched {
  enum {
    NoInstrModel	= 0,
    SCHED_LIST_END = 1
  };
} // End Sched namespace
} // End XCore namespace
} // End llvm namespace 
#endif // GET_INSTRINFO_ENUM

/*===- TableGen'erated file -------------------------------------*- C++ -*-===*\
|*                                                                            *|
|*Target Instruction Descriptors                                              *|
|*                                                                            *|
|* Automatically generated file, do not edit!                                 *|
|*                                                                            *|
\*===----------------------------------------------------------------------===*/


#ifdef GET_INSTRINFO_MC_DESC
#undef GET_INSTRINFO_MC_DESC
namespace llvm {

static const uint16_t ImplicitList1[] = { XCore::SP, 0 };
static const uint16_t ImplicitList2[] = { XCore::R0, XCore::R1, XCore::R2, XCore::R3, XCore::R11, XCore::LR, 0 };
static const uint16_t ImplicitList3[] = { XCore::R11, 0 };

static const MCOperandInfo OperandInfo2[] = { { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo3[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo4[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo5[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo6[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo7[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo8[] = { { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo9[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo10[] = { { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo11[] = { { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo12[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo13[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo14[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo15[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo16[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo17[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo18[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo19[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo20[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((1 << 16) | (1 << MCOI::TIED_TO)) }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo21[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo22[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo23[] = { { XCore::RRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo24[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo25[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo26[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((1 << 16) | (1 << MCOI::TIED_TO)) }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo27[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo28[] = { { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo29[] = { { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo30[] = { { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { XCore::GRRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };

extern const MCInstrDesc XCoreInsts[] = {
  { 0,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #0 = PHI
  { 1,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Variadic), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1 = INLINEASM
  { 2,	1,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::NotDuplicable)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #2 = CFI_INSTRUCTION
  { 3,	1,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::NotDuplicable)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #3 = EH_LABEL
  { 4,	1,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::NotDuplicable)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #4 = GC_LABEL
  { 5,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Variadic), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #5 = KILL
  { 6,	3,	1,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo3,0,nullptr },  // Inst #6 = EXTRACT_SUBREG
  { 7,	4,	1,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo4,0,nullptr },  // Inst #7 = INSERT_SUBREG
  { 8,	1,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #8 = IMPLICIT_DEF
  { 9,	4,	1,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo6,0,nullptr },  // Inst #9 = SUBREG_TO_REG
  { 10,	3,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::CheapAsAMove), 0x0ULL, nullptr, nullptr, OperandInfo3,0,nullptr },  // Inst #10 = COPY_TO_REGCLASS
  { 11,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Variadic), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #11 = DBG_VALUE
  { 12,	2,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Variadic)|(1<<MCID::CheapAsAMove), 0x0ULL, nullptr, nullptr, OperandInfo7,0,nullptr },  // Inst #12 = REG_SEQUENCE
  { 13,	2,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::CheapAsAMove), 0x0ULL, nullptr, nullptr, OperandInfo7,0,nullptr },  // Inst #13 = COPY
  { 14,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #14 = BUNDLE
  { 15,	1,	0,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #15 = LIFETIME_START
  { 16,	1,	0,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #16 = LIFETIME_END
  { 17,	2,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Call)|(1<<MCID::MayLoad)|(1<<MCID::UsesCustomInserter)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo8,0,nullptr },  // Inst #17 = STACKMAP
  { 18,	6,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Call)|(1<<MCID::MayLoad)|(1<<MCID::UsesCustomInserter)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo9,0,nullptr },  // Inst #18 = PATCHPOINT
  { 19,	1,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo10,0,nullptr },  // Inst #19 = LOAD_STACK_GUARD
  { 20,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Call)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #20 = STATEPOINT
  { 21,	2,	0,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo11,0,nullptr },  // Inst #21 = FRAME_ALLOC
  { 22,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #22 = ADD_2rus
  { 23,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #23 = ADD_3r
  { 24,	1,	0,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #24 = ADJCALLSTACKDOWN
  { 25,	2,	0,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo8,0,nullptr },  // Inst #25 = ADJCALLSTACKUP
  { 26,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #26 = ANDNOT_2r
  { 27,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #27 = AND_3r
  { 28,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #28 = ASHR_l2rus
  { 29,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #29 = ASHR_l3r
  { 30,	1,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #30 = BAU_1r
  { 31,	2,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #31 = BITREV_l2r
  { 32,	1,	0,	0,	4,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo2,0,nullptr },  // Inst #32 = BLACP_lu10
  { 33,	1,	0,	0,	2,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo2,0,nullptr },  // Inst #33 = BLACP_u10
  { 34,	1,	0,	0,	4,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, nullptr, OperandInfo2,0,nullptr },  // Inst #34 = BLAT_lu6
  { 35,	1,	0,	0,	2,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, nullptr, OperandInfo2,0,nullptr },  // Inst #35 = BLAT_u6
  { 36,	1,	0,	0,	2,	0|(1<<MCID::Call), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo15,0,nullptr },  // Inst #36 = BLA_1r
  { 37,	1,	0,	0,	4,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo5,0,nullptr },  // Inst #37 = BLRB_lu10
  { 38,	1,	0,	0,	2,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo5,0,nullptr },  // Inst #38 = BLRB_u10
  { 39,	1,	0,	0,	4,	0|(1<<MCID::Call), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo5,0,nullptr },  // Inst #39 = BLRF_lu10
  { 40,	1,	0,	0,	2,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList2, OperandInfo5,0,nullptr },  // Inst #40 = BLRF_u10
  { 41,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #41 = BRBF_lru6
  { 42,	2,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #42 = BRBF_ru6
  { 43,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #43 = BRBT_lru6
  { 44,	2,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #44 = BRBT_ru6
  { 45,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #45 = BRBU_lu6
  { 46,	1,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #46 = BRBU_u6
  { 47,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #47 = BRFF_lru6
  { 48,	2,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #48 = BRFF_ru6
  { 49,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #49 = BRFT_lru6
  { 50,	2,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #50 = BRFT_ru6
  { 51,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #51 = BRFU_lu6
  { 52,	1,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #52 = BRFU_u6
  { 53,	1,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #53 = BRU_1r
  { 54,	2,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo18,0,nullptr },  // Inst #54 = BR_JT
  { 55,	2,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo18,0,nullptr },  // Inst #55 = BR_JT32
  { 56,	2,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #56 = BYTEREV_l2r
  { 57,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #57 = CHKCT_2r
  { 58,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #58 = CHKCT_rus
  { 59,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #59 = CLRE_0R
  { 60,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #60 = CLRPT_1R
  { 61,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #61 = CLRSR_branch_lu6
  { 62,	1,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #62 = CLRSR_branch_u6
  { 63,	1,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #63 = CLRSR_lu6
  { 64,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #64 = CLRSR_u6
  { 65,	2,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #65 = CLZ_l2r
  { 66,	5,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #66 = CRC8_l4r
  { 67,	4,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #67 = CRC_l3r
  { 68,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #68 = DCALL_0R
  { 69,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, nullptr,0,nullptr },  // Inst #69 = DENTSP_0R
  { 70,	1,	1,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #70 = DGETREG_1r
  { 71,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #71 = DIVS_l3r
  { 72,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #72 = DIVU_l3r
  { 73,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList1, nullptr,0,nullptr },  // Inst #73 = DRESTSP_0R
  { 74,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #74 = DRET_0R
  { 75,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #75 = ECALLF_1r
  { 76,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #76 = ECALLT_1r
  { 77,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #77 = EDU_1r
  { 78,	2,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #78 = EEF_2r
  { 79,	2,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #79 = EET_2r
  { 80,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #80 = EEU_1r
  { 81,	2,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #81 = EH_RETURN
  { 82,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #82 = ENDIN_2r
  { 83,	1,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #83 = ENTSP_lu6
  { 84,	1,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #84 = ENTSP_u6
  { 85,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #85 = EQ_2rus
  { 86,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #86 = EQ_3r
  { 87,	1,	0,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #87 = EXTDP_lu6
  { 88,	1,	0,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #88 = EXTDP_u6
  { 89,	1,	0,	0,	4,	0, 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #89 = EXTSP_lu6
  { 90,	1,	0,	0,	2,	0, 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #90 = EXTSP_u6
  { 91,	1,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #91 = FRAME_TO_ARGS_OFFSET
  { 92,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #92 = FREER_1r
  { 93,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #93 = FREET_0R
  { 94,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #94 = GETD_l2r
  { 95,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList3, nullptr,0,nullptr },  // Inst #95 = GETED_0R
  { 96,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList3, nullptr,0,nullptr },  // Inst #96 = GETET_0R
  { 97,	0,	0,	0,	2,	0, 0x0ULL, nullptr, ImplicitList3, nullptr,0,nullptr },  // Inst #97 = GETID_0R
  { 98,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList3, nullptr,0,nullptr },  // Inst #98 = GETKEP_0R
  { 99,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList3, nullptr,0,nullptr },  // Inst #99 = GETKSP_0R
  { 100,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #100 = GETN_l2r
  { 101,	2,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #101 = GETPS_l2r
  { 102,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #102 = GETR_rus
  { 103,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #103 = GETSR_lu6
  { 104,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #104 = GETSR_u6
  { 105,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #105 = GETST_2r
  { 106,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #106 = GETTS_2r
  { 107,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #107 = INCT_2r
  { 108,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #108 = INITCP_2r
  { 109,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #109 = INITDP_2r
  { 110,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #110 = INITLR_l2r
  { 111,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #111 = INITPC_2r
  { 112,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #112 = INITSP_2r
  { 113,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #113 = INPW_l2rus
  { 114,	3,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #114 = INSHR_2r
  { 115,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #115 = INT_2r
  { 116,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #116 = IN_2r
  { 117,	0,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #117 = Int_MemBarrier
  { 118,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #118 = KCALL_1r
  { 119,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #119 = KCALL_lu6
  { 120,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #120 = KCALL_u6
  { 121,	1,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #121 = KENTSP_lu6
  { 122,	1,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #122 = KENTSP_u6
  { 123,	1,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #123 = KRESTSP_lu6
  { 124,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #124 = KRESTSP_u6
  { 125,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList1, nullptr,0,nullptr },  // Inst #125 = KRET_0R
  { 126,	5,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #126 = LADD_l5r
  { 127,	3,	1,	0,	2,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #127 = LD16S_3r
  { 128,	3,	1,	0,	2,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #128 = LD8U_3r
  { 129,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #129 = LDA16B_l3r
  { 130,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #130 = LDA16F_l3r
  { 131,	1,	0,	0,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #131 = LDAPB_lu10
  { 132,	1,	0,	0,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #132 = LDAPB_u10
  { 133,	1,	0,	0,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #133 = LDAPF_lu10
  { 134,	1,	0,	0,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #134 = LDAPF_lu10_ba
  { 135,	1,	0,	0,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #135 = LDAPF_u10
  { 136,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #136 = LDAWB_l2rus
  { 137,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #137 = LDAWB_l3r
  { 138,	1,	0,	0,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #138 = LDAWCP_lu6
  { 139,	1,	0,	0,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #139 = LDAWCP_u6
  { 140,	2,	1,	0,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #140 = LDAWDP_lru6
  { 141,	2,	1,	0,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #141 = LDAWDP_ru6
  { 142,	3,	1,	0,	0,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo24,0,nullptr },  // Inst #142 = LDAWFI
  { 143,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #143 = LDAWF_l2rus
  { 144,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #144 = LDAWF_l3r
  { 145,	2,	1,	0,	4,	0, 0x0ULL, ImplicitList1, nullptr, OperandInfo23,0,nullptr },  // Inst #145 = LDAWSP_lru6
  { 146,	2,	1,	0,	2,	0, 0x0ULL, ImplicitList1, nullptr, OperandInfo23,0,nullptr },  // Inst #146 = LDAWSP_ru6
  { 147,	2,	1,	0,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #147 = LDC_lru6
  { 148,	2,	1,	0,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #148 = LDC_ru6
  { 149,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #149 = LDET_0R
  { 150,	5,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #150 = LDIVU_l5r
  { 151,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #151 = LDSED_0R
  { 152,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #152 = LDSPC_0R
  { 153,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #153 = LDSSR_0R
  { 154,	2,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #154 = LDWCP_lru6
  { 155,	1,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #155 = LDWCP_lu10
  { 156,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #156 = LDWCP_ru6
  { 157,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #157 = LDWCP_u10
  { 158,	2,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #158 = LDWDP_lru6
  { 159,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #159 = LDWDP_ru6
  { 160,	3,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo24,0,nullptr },  // Inst #160 = LDWFI
  { 161,	2,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x0ULL, ImplicitList1, nullptr, OperandInfo23,0,nullptr },  // Inst #161 = LDWSP_lru6
  { 162,	2,	1,	0,	2,	0|(1<<MCID::MayLoad), 0x0ULL, ImplicitList1, nullptr, OperandInfo23,0,nullptr },  // Inst #162 = LDWSP_ru6
  { 163,	3,	1,	0,	2,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #163 = LDW_2rus
  { 164,	3,	1,	0,	2,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #164 = LDW_3r
  { 165,	6,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #165 = LMUL_l6r
  { 166,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #166 = LSS_3r
  { 167,	5,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #167 = LSUB_l5r
  { 168,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #168 = LSU_3r
  { 169,	6,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #169 = MACCS_l4r
  { 170,	6,	2,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #170 = MACCU_l4r
  { 171,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #171 = MJOIN_1r
  { 172,	2,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #172 = MKMSK_2r
  { 173,	2,	1,	0,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #173 = MKMSK_rus
  { 174,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #174 = MSYNC_1r
  { 175,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #175 = MUL_l3r
  { 176,	2,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #176 = NEG
  { 177,	2,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #177 = NOT
  { 178,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #178 = OR_3r
  { 179,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #179 = OUTCT_2r
  { 180,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #180 = OUTCT_rus
  { 181,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #181 = OUTPW_l2rus
  { 182,	3,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #182 = OUTSHR_2r
  { 183,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #183 = OUTT_2r
  { 184,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #184 = OUT_2r
  { 185,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #185 = PEEK_2r
  { 186,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #186 = REMS_l3r
  { 187,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #187 = REMU_l3r
  { 188,	1,	0,	0,	4,	0|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::MayLoad)|(1<<MCID::Terminator), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #188 = RETSP_lu6
  { 189,	1,	0,	0,	2,	0|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::MayLoad)|(1<<MCID::Terminator), 0x0ULL, ImplicitList1, ImplicitList1, OperandInfo2,0,nullptr },  // Inst #189 = RETSP_u6
  { 190,	4,	1,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #190 = SELECT_CC
  { 191,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #191 = SETCLK_l2r
  { 192,	1,	0,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #192 = SETCP_1r
  { 193,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #193 = SETC_l2r
  { 194,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #194 = SETC_lru6
  { 195,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #195 = SETC_ru6
  { 196,	1,	0,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #196 = SETDP_1r
  { 197,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #197 = SETD_2r
  { 198,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, nullptr, OperandInfo15,0,nullptr },  // Inst #198 = SETEV_1r
  { 199,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, nullptr, nullptr,0,nullptr },  // Inst #199 = SETKEP_0R
  { 200,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #200 = SETN_l2r
  { 201,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #201 = SETPSC_2r
  { 202,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #202 = SETPS_l2r
  { 203,	2,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #203 = SETPT_2r
  { 204,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #204 = SETRDY_l2r
  { 205,	1,	0,	0,	2,	0, 0x0ULL, nullptr, ImplicitList1, OperandInfo15,0,nullptr },  // Inst #205 = SETSP_1r
  { 206,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #206 = SETSR_branch_lu6
  { 207,	1,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #207 = SETSR_branch_u6
  { 208,	1,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #208 = SETSR_lu6
  { 209,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #209 = SETSR_u6
  { 210,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #210 = SETTW_l2r
  { 211,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, nullptr, OperandInfo15,0,nullptr },  // Inst #211 = SETV_1r
  { 212,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #212 = SEXT_2r
  { 213,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #213 = SEXT_rus
  { 214,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #214 = SHL_2rus
  { 215,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #215 = SHL_3r
  { 216,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #216 = SHR_2rus
  { 217,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #217 = SHR_3r
  { 218,	0,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #218 = SSYNC_0r
  { 219,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #219 = ST16_l3r
  { 220,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #220 = ST8_l3r
  { 221,	0,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #221 = STET_0R
  { 222,	0,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #222 = STSED_0R
  { 223,	0,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #223 = STSPC_0R
  { 224,	0,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList1, nullptr, nullptr,0,nullptr },  // Inst #224 = STSSR_0R
  { 225,	2,	0,	0,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #225 = STWDP_lru6
  { 226,	2,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #226 = STWDP_ru6
  { 227,	3,	0,	0,	0,	0|(1<<MCID::Pseudo)|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo24,0,nullptr },  // Inst #227 = STWFI
  { 228,	2,	0,	0,	4,	0|(1<<MCID::MayStore), 0x0ULL, ImplicitList1, nullptr, OperandInfo23,0,nullptr },  // Inst #228 = STWSP_lru6
  { 229,	2,	0,	0,	2,	0|(1<<MCID::MayStore), 0x0ULL, ImplicitList1, nullptr, OperandInfo23,0,nullptr },  // Inst #229 = STWSP_ru6
  { 230,	3,	0,	0,	2,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #230 = STW_2rus
  { 231,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #231 = STW_l3r
  { 232,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #232 = SUB_2rus
  { 233,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #233 = SUB_3r
  { 234,	1,	0,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #234 = SYNCR_1r
  { 235,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #235 = TESTCT_2r
  { 236,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #236 = TESTLCL_l2r
  { 237,	2,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #237 = TESTWCT_2r
  { 238,	2,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #238 = TSETMR_2r
  { 239,	3,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo30,0,nullptr },  // Inst #239 = TSETR_3r
  { 240,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #240 = TSTART_1R
  { 241,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #241 = WAITEF_1R
  { 242,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #242 = WAITET_1R
  { 243,	0,	0,	0,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::MayLoad)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #243 = WAITEU_0R
  { 244,	3,	1,	0,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #244 = XOR_l3r
  { 245,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #245 = ZEXT_2r
  { 246,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #246 = ZEXT_rus
};

extern const char XCoreInstrNameData[] = {
  /* 0 */ 'L', 'D', 'A', 'P', 'B', '_', 'u', '1', '0', 0,
  /* 10 */ 'B', 'L', 'R', 'B', '_', 'u', '1', '0', 0,
  /* 19 */ 'L', 'D', 'A', 'P', 'F', '_', 'u', '1', '0', 0,
  /* 29 */ 'B', 'L', 'R', 'F', '_', 'u', '1', '0', 0,
  /* 38 */ 'B', 'L', 'A', 'C', 'P', '_', 'u', '1', '0', 0,
  /* 48 */ 'L', 'D', 'W', 'C', 'P', '_', 'u', '1', '0', 0,
  /* 58 */ 'L', 'D', 'A', 'P', 'B', '_', 'l', 'u', '1', '0', 0,
  /* 69 */ 'B', 'L', 'R', 'B', '_', 'l', 'u', '1', '0', 0,
  /* 79 */ 'L', 'D', 'A', 'P', 'F', '_', 'l', 'u', '1', '0', 0,
  /* 90 */ 'B', 'L', 'R', 'F', '_', 'l', 'u', '1', '0', 0,
  /* 100 */ 'B', 'L', 'A', 'C', 'P', '_', 'l', 'u', '1', '0', 0,
  /* 111 */ 'L', 'D', 'W', 'C', 'P', '_', 'l', 'u', '1', '0', 0,
  /* 122 */ 'B', 'R', '_', 'J', 'T', '3', '2', 0,
  /* 130 */ 'K', 'C', 'A', 'L', 'L', '_', 'u', '6', 0,
  /* 139 */ 'L', 'D', 'A', 'W', 'C', 'P', '_', 'u', '6', 0,
  /* 149 */ 'E', 'X', 'T', 'D', 'P', '_', 'u', '6', 0,
  /* 158 */ 'R', 'E', 'T', 'S', 'P', '_', 'u', '6', 0,
  /* 167 */ 'K', 'E', 'N', 'T', 'S', 'P', '_', 'u', '6', 0,
  /* 177 */ 'K', 'R', 'E', 'S', 'T', 'S', 'P', '_', 'u', '6', 0,
  /* 188 */ 'E', 'X', 'T', 'S', 'P', '_', 'u', '6', 0,
  /* 197 */ 'C', 'L', 'R', 'S', 'R', '_', 'u', '6', 0,
  /* 206 */ 'G', 'E', 'T', 'S', 'R', '_', 'u', '6', 0,
  /* 215 */ 'S', 'E', 'T', 'S', 'R', '_', 'u', '6', 0,
  /* 224 */ 'B', 'L', 'A', 'T', '_', 'u', '6', 0,
  /* 232 */ 'B', 'R', 'B', 'U', '_', 'u', '6', 0,
  /* 240 */ 'B', 'R', 'F', 'U', '_', 'u', '6', 0,
  /* 248 */ 'C', 'L', 'R', 'S', 'R', '_', 'b', 'r', 'a', 'n', 'c', 'h', '_', 'u', '6', 0,
  /* 264 */ 'S', 'E', 'T', 'S', 'R', '_', 'b', 'r', 'a', 'n', 'c', 'h', '_', 'u', '6', 0,
  /* 280 */ 'K', 'C', 'A', 'L', 'L', '_', 'l', 'u', '6', 0,
  /* 290 */ 'L', 'D', 'A', 'W', 'C', 'P', '_', 'l', 'u', '6', 0,
  /* 301 */ 'E', 'X', 'T', 'D', 'P', '_', 'l', 'u', '6', 0,
  /* 311 */ 'R', 'E', 'T', 'S', 'P', '_', 'l', 'u', '6', 0,
  /* 321 */ 'K', 'E', 'N', 'T', 'S', 'P', '_', 'l', 'u', '6', 0,
  /* 332 */ 'K', 'R', 'E', 'S', 'T', 'S', 'P', '_', 'l', 'u', '6', 0,
  /* 344 */ 'E', 'X', 'T', 'S', 'P', '_', 'l', 'u', '6', 0,
  /* 354 */ 'C', 'L', 'R', 'S', 'R', '_', 'l', 'u', '6', 0,
  /* 364 */ 'G', 'E', 'T', 'S', 'R', '_', 'l', 'u', '6', 0,
  /* 374 */ 'S', 'E', 'T', 'S', 'R', '_', 'l', 'u', '6', 0,
  /* 384 */ 'B', 'L', 'A', 'T', '_', 'l', 'u', '6', 0,
  /* 393 */ 'B', 'R', 'B', 'U', '_', 'l', 'u', '6', 0,
  /* 402 */ 'B', 'R', 'F', 'U', '_', 'l', 'u', '6', 0,
  /* 411 */ 'C', 'L', 'R', 'S', 'R', '_', 'b', 'r', 'a', 'n', 'c', 'h', '_', 'l', 'u', '6', 0,
  /* 428 */ 'S', 'E', 'T', 'S', 'R', '_', 'b', 'r', 'a', 'n', 'c', 'h', '_', 'l', 'u', '6', 0,
  /* 445 */ 'L', 'D', 'C', '_', 'r', 'u', '6', 0,
  /* 453 */ 'S', 'E', 'T', 'C', '_', 'r', 'u', '6', 0,
  /* 462 */ 'B', 'R', 'B', 'F', '_', 'r', 'u', '6', 0,
  /* 471 */ 'B', 'R', 'F', 'F', '_', 'r', 'u', '6', 0,
  /* 480 */ 'L', 'D', 'W', 'C', 'P', '_', 'r', 'u', '6', 0,
  /* 490 */ 'L', 'D', 'A', 'W', 'D', 'P', '_', 'r', 'u', '6', 0,
  /* 501 */ 'L', 'D', 'W', 'D', 'P', '_', 'r', 'u', '6', 0,
  /* 511 */ 'S', 'T', 'W', 'D', 'P', '_', 'r', 'u', '6', 0,
  /* 521 */ 'L', 'D', 'A', 'W', 'S', 'P', '_', 'r', 'u', '6', 0,
  /* 532 */ 'L', 'D', 'W', 'S', 'P', '_', 'r', 'u', '6', 0,
  /* 542 */ 'S', 'T', 'W', 'S', 'P', '_', 'r', 'u', '6', 0,
  /* 552 */ 'B', 'R', 'B', 'T', '_', 'r', 'u', '6', 0,
  /* 561 */ 'B', 'R', 'F', 'T', '_', 'r', 'u', '6', 0,
  /* 570 */ 'L', 'D', 'C', '_', 'l', 'r', 'u', '6', 0,
  /* 579 */ 'S', 'E', 'T', 'C', '_', 'l', 'r', 'u', '6', 0,
  /* 589 */ 'B', 'R', 'B', 'F', '_', 'l', 'r', 'u', '6', 0,
  /* 599 */ 'B', 'R', 'F', 'F', '_', 'l', 'r', 'u', '6', 0,
  /* 609 */ 'L', 'D', 'W', 'C', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 620 */ 'L', 'D', 'A', 'W', 'D', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 632 */ 'L', 'D', 'W', 'D', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 643 */ 'S', 'T', 'W', 'D', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 654 */ 'L', 'D', 'A', 'W', 'S', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 666 */ 'L', 'D', 'W', 'S', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 677 */ 'S', 'T', 'W', 'S', 'P', '_', 'l', 'r', 'u', '6', 0,
  /* 688 */ 'B', 'R', 'B', 'T', '_', 'l', 'r', 'u', '6', 0,
  /* 698 */ 'B', 'R', 'F', 'T', '_', 'l', 'r', 'u', '6', 0,
  /* 708 */ 'S', 'E', 'L', 'E', 'C', 'T', '_', 'C', 'C', 0,
  /* 718 */ 'F', 'R', 'A', 'M', 'E', '_', 'A', 'L', 'L', 'O', 'C', 0,
  /* 730 */ 'L', 'I', 'F', 'E', 'T', 'I', 'M', 'E', '_', 'E', 'N', 'D', 0,
  /* 743 */ 'L', 'O', 'A', 'D', '_', 'S', 'T', 'A', 'C', 'K', '_', 'G', 'U', 'A', 'R', 'D', 0,
  /* 760 */ 'R', 'E', 'G', '_', 'S', 'E', 'Q', 'U', 'E', 'N', 'C', 'E', 0,
  /* 773 */ 'B', 'U', 'N', 'D', 'L', 'E', 0,
  /* 780 */ 'D', 'B', 'G', '_', 'V', 'A', 'L', 'U', 'E', 0,
  /* 790 */ 'I', 'M', 'P', 'L', 'I', 'C', 'I', 'T', '_', 'D', 'E', 'F', 0,
  /* 803 */ 'N', 'E', 'G', 0,
  /* 807 */ 'E', 'X', 'T', 'R', 'A', 'C', 'T', '_', 'S', 'U', 'B', 'R', 'E', 'G', 0,
  /* 822 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'S', 'U', 'B', 'R', 'E', 'G', 0,
  /* 836 */ 'S', 'U', 'B', 'R', 'E', 'G', '_', 'T', 'O', '_', 'R', 'E', 'G', 0,
  /* 850 */ 'L', 'D', 'A', 'W', 'F', 'I', 0,
  /* 857 */ 'L', 'D', 'W', 'F', 'I', 0,
  /* 863 */ 'S', 'T', 'W', 'F', 'I', 0,
  /* 869 */ 'P', 'H', 'I', 0,
  /* 873 */ 'G', 'C', '_', 'L', 'A', 'B', 'E', 'L', 0,
  /* 882 */ 'E', 'H', '_', 'L', 'A', 'B', 'E', 'L', 0,
  /* 891 */ 'K', 'I', 'L', 'L', 0,
  /* 896 */ 'I', 'N', 'L', 'I', 'N', 'E', 'A', 'S', 'M', 0,
  /* 906 */ 'C', 'F', 'I', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', 0,
  /* 922 */ 'E', 'H', '_', 'R', 'E', 'T', 'U', 'R', 'N', 0,
  /* 932 */ 'A', 'D', 'J', 'C', 'A', 'L', 'L', 'S', 'T', 'A', 'C', 'K', 'D', 'O', 'W', 'N', 0,
  /* 949 */ 'S', 'T', 'A', 'C', 'K', 'M', 'A', 'P', 0,
  /* 958 */ 'A', 'D', 'J', 'C', 'A', 'L', 'L', 'S', 'T', 'A', 'C', 'K', 'U', 'P', 0,
  /* 973 */ 'L', 'D', 'S', 'P', 'C', '_', '0', 'R', 0,
  /* 982 */ 'S', 'T', 'S', 'P', 'C', '_', '0', 'R', 0,
  /* 991 */ 'L', 'D', 'S', 'E', 'D', '_', '0', 'R', 0,
  /* 1000 */ 'S', 'T', 'S', 'E', 'D', '_', '0', 'R', 0,
  /* 1009 */ 'G', 'E', 'T', 'E', 'D', '_', '0', 'R', 0,
  /* 1018 */ 'G', 'E', 'T', 'I', 'D', '_', '0', 'R', 0,
  /* 1027 */ 'C', 'L', 'R', 'E', '_', '0', 'R', 0,
  /* 1035 */ 'D', 'C', 'A', 'L', 'L', '_', '0', 'R', 0,
  /* 1044 */ 'G', 'E', 'T', 'K', 'E', 'P', '_', '0', 'R', 0,
  /* 1054 */ 'S', 'E', 'T', 'K', 'E', 'P', '_', '0', 'R', 0,
  /* 1064 */ 'G', 'E', 'T', 'K', 'S', 'P', '_', '0', 'R', 0,
  /* 1074 */ 'D', 'E', 'N', 'T', 'S', 'P', '_', '0', 'R', 0,
  /* 1084 */ 'D', 'R', 'E', 'S', 'T', 'S', 'P', '_', '0', 'R', 0,
  /* 1095 */ 'L', 'D', 'S', 'S', 'R', '_', '0', 'R', 0,
  /* 1104 */ 'S', 'T', 'S', 'S', 'R', '_', '0', 'R', 0,
  /* 1113 */ 'L', 'D', 'E', 'T', '_', '0', 'R', 0,
  /* 1121 */ 'F', 'R', 'E', 'E', 'T', '_', '0', 'R', 0,
  /* 1130 */ 'D', 'R', 'E', 'T', '_', '0', 'R', 0,
  /* 1138 */ 'K', 'R', 'E', 'T', '_', '0', 'R', 0,
  /* 1146 */ 'G', 'E', 'T', 'E', 'T', '_', '0', 'R', 0,
  /* 1155 */ 'S', 'T', 'E', 'T', '_', '0', 'R', 0,
  /* 1163 */ 'W', 'A', 'I', 'T', 'E', 'U', '_', '0', 'R', 0,
  /* 1173 */ 'W', 'A', 'I', 'T', 'E', 'F', '_', '1', 'R', 0,
  /* 1183 */ 'W', 'A', 'I', 'T', 'E', 'T', '_', '1', 'R', 0,
  /* 1193 */ 'C', 'L', 'R', 'P', 'T', '_', '1', 'R', 0,
  /* 1202 */ 'T', 'S', 'T', 'A', 'R', 'T', '_', '1', 'R', 0,
  /* 1212 */ 'C', 'O', 'P', 'Y', '_', 'T', 'O', '_', 'R', 'E', 'G', 'C', 'L', 'A', 'S', 'S', 0,
  /* 1229 */ 'F', 'R', 'A', 'M', 'E', '_', 'T', 'O', '_', 'A', 'R', 'G', 'S', '_', 'O', 'F', 'F', 'S', 'E', 'T', 0,
  /* 1250 */ 'B', 'R', '_', 'J', 'T', 0,
  /* 1256 */ 'S', 'T', 'A', 'T', 'E', 'P', 'O', 'I', 'N', 'T', 0,
  /* 1267 */ 'P', 'A', 'T', 'C', 'H', 'P', 'O', 'I', 'N', 'T', 0,
  /* 1278 */ 'N', 'O', 'T', 0,
  /* 1282 */ 'L', 'I', 'F', 'E', 'T', 'I', 'M', 'E', '_', 'S', 'T', 'A', 'R', 'T', 0,
  /* 1297 */ 'C', 'O', 'P', 'Y', 0,
  /* 1302 */ 'L', 'D', 'A', 'P', 'F', '_', 'l', 'u', '1', '0', '_', 'b', 'a', 0,
  /* 1316 */ 'S', 'S', 'Y', 'N', 'C', '_', '0', 'r', 0,
  /* 1325 */ 'B', 'L', 'A', '_', '1', 'r', 0,
  /* 1332 */ 'M', 'S', 'Y', 'N', 'C', '_', '1', 'r', 0,
  /* 1341 */ 'E', 'C', 'A', 'L', 'L', 'F', '_', '1', 'r', 0,
  /* 1351 */ 'D', 'G', 'E', 'T', 'R', 'E', 'G', '_', '1', 'r', 0,
  /* 1362 */ 'K', 'C', 'A', 'L', 'L', '_', '1', 'r', 0,
  /* 1371 */ 'M', 'J', 'O', 'I', 'N', '_', '1', 'r', 0,
  /* 1380 */ 'S', 'E', 'T', 'C', 'P', '_', '1', 'r', 0,
  /* 1389 */ 'S', 'E', 'T', 'D', 'P', '_', '1', 'r', 0,
  /* 1398 */ 'S', 'E', 'T', 'S', 'P', '_', '1', 'r', 0,
  /* 1407 */ 'S', 'Y', 'N', 'C', 'R', '_', '1', 'r', 0,
  /* 1416 */ 'F', 'R', 'E', 'E', 'R', '_', '1', 'r', 0,
  /* 1425 */ 'E', 'C', 'A', 'L', 'L', 'T', '_', '1', 'r', 0,
  /* 1435 */ 'B', 'A', 'U', '_', '1', 'r', 0,
  /* 1442 */ 'E', 'D', 'U', '_', '1', 'r', 0,
  /* 1449 */ 'E', 'E', 'U', '_', '1', 'r', 0,
  /* 1456 */ 'B', 'R', 'U', '_', '1', 'r', 0,
  /* 1463 */ 'S', 'E', 'T', 'E', 'V', '_', '1', 'r', 0,
  /* 1472 */ 'S', 'E', 'T', 'V', '_', '1', 'r', 0,
  /* 1480 */ 'I', 'N', 'I', 'T', 'P', 'C', '_', '2', 'r', 0,
  /* 1490 */ 'S', 'E', 'T', 'P', 'S', 'C', '_', '2', 'r', 0,
  /* 1500 */ 'S', 'E', 'T', 'D', '_', '2', 'r', 0,
  /* 1508 */ 'E', 'E', 'F', '_', '2', 'r', 0,
  /* 1515 */ 'P', 'E', 'E', 'K', '_', '2', 'r', 0,
  /* 1523 */ 'M', 'K', 'M', 'S', 'K', '_', '2', 'r', 0,
  /* 1532 */ 'E', 'N', 'D', 'I', 'N', '_', '2', 'r', 0,
  /* 1541 */ 'I', 'N', 'I', 'T', 'C', 'P', '_', '2', 'r', 0,
  /* 1551 */ 'I', 'N', 'I', 'T', 'D', 'P', '_', '2', 'r', 0,
  /* 1561 */ 'I', 'N', 'I', 'T', 'S', 'P', '_', '2', 'r', 0,
  /* 1571 */ 'I', 'N', 'S', 'H', 'R', '_', '2', 'r', 0,
  /* 1580 */ 'O', 'U', 'T', 'S', 'H', 'R', '_', '2', 'r', 0,
  /* 1590 */ 'T', 'S', 'E', 'T', 'M', 'R', '_', '2', 'r', 0,
  /* 1600 */ 'G', 'E', 'T', 'T', 'S', '_', '2', 'r', 0,
  /* 1609 */ 'C', 'H', 'K', 'C', 'T', '_', '2', 'r', 0,
  /* 1618 */ 'I', 'N', 'C', 'T', '_', '2', 'r', 0,
  /* 1626 */ 'T', 'E', 'S', 'T', 'C', 'T', '_', '2', 'r', 0,
  /* 1636 */ 'O', 'U', 'T', 'C', 'T', '_', '2', 'r', 0,
  /* 1645 */ 'T', 'E', 'S', 'T', 'W', 'C', 'T', '_', '2', 'r', 0,
  /* 1656 */ 'E', 'E', 'T', '_', '2', 'r', 0,
  /* 1663 */ 'I', 'N', 'T', '_', '2', 'r', 0,
  /* 1670 */ 'A', 'N', 'D', 'N', 'O', 'T', '_', '2', 'r', 0,
  /* 1680 */ 'S', 'E', 'T', 'P', 'T', '_', '2', 'r', 0,
  /* 1689 */ 'G', 'E', 'T', 'S', 'T', '_', '2', 'r', 0,
  /* 1698 */ 'O', 'U', 'T', 'T', '_', '2', 'r', 0,
  /* 1706 */ 'O', 'U', 'T', '_', '2', 'r', 0,
  /* 1713 */ 'S', 'E', 'X', 'T', '_', '2', 'r', 0,
  /* 1721 */ 'Z', 'E', 'X', 'T', '_', '2', 'r', 0,
  /* 1729 */ 'S', 'E', 'T', 'C', '_', 'l', '2', 'r', 0,
  /* 1738 */ 'G', 'E', 'T', 'D', '_', 'l', '2', 'r', 0,
  /* 1747 */ 'S', 'E', 'T', 'C', 'L', 'K', '_', 'l', '2', 'r', 0,
  /* 1758 */ 'T', 'E', 'S', 'T', 'L', 'C', 'L', '_', 'l', '2', 'r', 0,
  /* 1770 */ 'G', 'E', 'T', 'N', '_', 'l', '2', 'r', 0,
  /* 1779 */ 'S', 'E', 'T', 'N', '_', 'l', '2', 'r', 0,
  /* 1788 */ 'I', 'N', 'I', 'T', 'L', 'R', '_', 'l', '2', 'r', 0,
  /* 1799 */ 'G', 'E', 'T', 'P', 'S', '_', 'l', '2', 'r', 0,
  /* 1809 */ 'S', 'E', 'T', 'P', 'S', '_', 'l', '2', 'r', 0,
  /* 1819 */ 'B', 'Y', 'T', 'E', 'R', 'E', 'V', '_', 'l', '2', 'r', 0,
  /* 1831 */ 'B', 'I', 'T', 'R', 'E', 'V', '_', 'l', '2', 'r', 0,
  /* 1842 */ 'S', 'E', 'T', 'T', 'W', '_', 'l', '2', 'r', 0,
  /* 1852 */ 'S', 'E', 'T', 'R', 'D', 'Y', '_', 'l', '2', 'r', 0,
  /* 1863 */ 'C', 'L', 'Z', '_', 'l', '2', 'r', 0,
  /* 1871 */ 'S', 'U', 'B', '_', '3', 'r', 0,
  /* 1878 */ 'A', 'D', 'D', '_', '3', 'r', 0,
  /* 1885 */ 'A', 'N', 'D', '_', '3', 'r', 0,
  /* 1892 */ 'S', 'H', 'L', '_', '3', 'r', 0,
  /* 1899 */ 'E', 'Q', '_', '3', 'r', 0,
  /* 1905 */ 'S', 'H', 'R', '_', '3', 'r', 0,
  /* 1912 */ 'O', 'R', '_', '3', 'r', 0,
  /* 1918 */ 'T', 'S', 'E', 'T', 'R', '_', '3', 'r', 0,
  /* 1927 */ 'L', 'D', '1', '6', 'S', '_', '3', 'r', 0,
  /* 1936 */ 'L', 'S', 'S', '_', '3', 'r', 0,
  /* 1943 */ 'L', 'D', '8', 'U', '_', '3', 'r', 0,
  /* 1951 */ 'L', 'S', 'U', '_', '3', 'r', 0,
  /* 1958 */ 'L', 'D', 'W', '_', '3', 'r', 0,
  /* 1965 */ 'S', 'T', '1', '6', '_', 'l', '3', 'r', 0,
  /* 1974 */ 'S', 'T', '8', '_', 'l', '3', 'r', 0,
  /* 1982 */ 'L', 'D', 'A', '1', '6', 'B', '_', 'l', '3', 'r', 0,
  /* 1993 */ 'L', 'D', 'A', 'W', 'B', '_', 'l', '3', 'r', 0,
  /* 2003 */ 'C', 'R', 'C', '_', 'l', '3', 'r', 0,
  /* 2011 */ 'L', 'D', 'A', '1', '6', 'F', '_', 'l', '3', 'r', 0,
  /* 2022 */ 'L', 'D', 'A', 'W', 'F', '_', 'l', '3', 'r', 0,
  /* 2032 */ 'M', 'U', 'L', '_', 'l', '3', 'r', 0,
  /* 2040 */ 'A', 'S', 'H', 'R', '_', 'l', '3', 'r', 0,
  /* 2049 */ 'X', 'O', 'R', '_', 'l', '3', 'r', 0,
  /* 2057 */ 'R', 'E', 'M', 'S', '_', 'l', '3', 'r', 0,
  /* 2066 */ 'D', 'I', 'V', 'S', '_', 'l', '3', 'r', 0,
  /* 2075 */ 'R', 'E', 'M', 'U', '_', 'l', '3', 'r', 0,
  /* 2084 */ 'D', 'I', 'V', 'U', '_', 'l', '3', 'r', 0,
  /* 2093 */ 'S', 'T', 'W', '_', 'l', '3', 'r', 0,
  /* 2101 */ 'C', 'R', 'C', '8', '_', 'l', '4', 'r', 0,
  /* 2110 */ 'M', 'A', 'C', 'C', 'S', '_', 'l', '4', 'r', 0,
  /* 2120 */ 'M', 'A', 'C', 'C', 'U', '_', 'l', '4', 'r', 0,
  /* 2130 */ 'L', 'S', 'U', 'B', '_', 'l', '5', 'r', 0,
  /* 2139 */ 'L', 'A', 'D', 'D', '_', 'l', '5', 'r', 0,
  /* 2148 */ 'L', 'D', 'I', 'V', 'U', '_', 'l', '5', 'r', 0,
  /* 2158 */ 'L', 'M', 'U', 'L', '_', 'l', '6', 'r', 0,
  /* 2167 */ 'I', 'n', 't', '_', 'M', 'e', 'm', 'B', 'a', 'r', 'r', 'i', 'e', 'r', 0,
  /* 2182 */ 'S', 'U', 'B', '_', '2', 'r', 'u', 's', 0,
  /* 2191 */ 'A', 'D', 'D', '_', '2', 'r', 'u', 's', 0,
  /* 2200 */ 'S', 'H', 'L', '_', '2', 'r', 'u', 's', 0,
  /* 2209 */ 'E', 'Q', '_', '2', 'r', 'u', 's', 0,
  /* 2217 */ 'S', 'H', 'R', '_', '2', 'r', 'u', 's', 0,
  /* 2226 */ 'L', 'D', 'W', '_', '2', 'r', 'u', 's', 0,
  /* 2235 */ 'S', 'T', 'W', '_', '2', 'r', 'u', 's', 0,
  /* 2244 */ 'L', 'D', 'A', 'W', 'B', '_', 'l', '2', 'r', 'u', 's', 0,
  /* 2256 */ 'L', 'D', 'A', 'W', 'F', '_', 'l', '2', 'r', 'u', 's', 0,
  /* 2268 */ 'A', 'S', 'H', 'R', '_', 'l', '2', 'r', 'u', 's', 0,
  /* 2279 */ 'I', 'N', 'P', 'W', '_', 'l', '2', 'r', 'u', 's', 0,
  /* 2290 */ 'O', 'U', 'T', 'P', 'W', '_', 'l', '2', 'r', 'u', 's', 0,
  /* 2302 */ 'M', 'K', 'M', 'S', 'K', '_', 'r', 'u', 's', 0,
  /* 2312 */ 'G', 'E', 'T', 'R', '_', 'r', 'u', 's', 0,
  /* 2321 */ 'C', 'H', 'K', 'C', 'T', '_', 'r', 'u', 's', 0,
  /* 2331 */ 'O', 'U', 'T', 'C', 'T', '_', 'r', 'u', 's', 0,
  /* 2341 */ 'S', 'E', 'X', 'T', '_', 'r', 'u', 's', 0,
  /* 2350 */ 'Z', 'E', 'X', 'T', '_', 'r', 'u', 's', 0,
};

extern const unsigned XCoreInstrNameIndices[] = {
    869U, 896U, 906U, 882U, 873U, 891U, 807U, 822U, 
    790U, 836U, 1212U, 780U, 760U, 1297U, 773U, 1282U, 
    730U, 949U, 1267U, 743U, 1256U, 718U, 2191U, 1878U, 
    932U, 958U, 1670U, 1885U, 2268U, 2040U, 1435U, 1831U, 
    100U, 38U, 384U, 224U, 1325U, 69U, 10U, 90U, 
    29U, 589U, 462U, 688U, 552U, 393U, 232U, 599U, 
    471U, 698U, 561U, 402U, 240U, 1456U, 1250U, 122U, 
    1819U, 1609U, 2321U, 1027U, 1193U, 411U, 248U, 354U, 
    197U, 1863U, 2101U, 2003U, 1035U, 1074U, 1351U, 2066U, 
    2084U, 1084U, 1130U, 1341U, 1425U, 1442U, 1508U, 1656U, 
    1449U, 922U, 1532U, 322U, 168U, 2209U, 1899U, 301U, 
    149U, 344U, 188U, 1229U, 1416U, 1121U, 1738U, 1009U, 
    1146U, 1018U, 1044U, 1064U, 1770U, 1799U, 2312U, 364U, 
    206U, 1689U, 1600U, 1618U, 1541U, 1551U, 1788U, 1480U, 
    1561U, 2279U, 1571U, 1663U, 1535U, 2167U, 1362U, 280U, 
    130U, 321U, 167U, 332U, 177U, 1138U, 2139U, 1927U, 
    1943U, 1982U, 2011U, 58U, 0U, 79U, 1302U, 19U, 
    2244U, 1993U, 290U, 139U, 620U, 490U, 850U, 2256U, 
    2022U, 654U, 521U, 570U, 445U, 1113U, 2148U, 991U, 
    973U, 1095U, 609U, 111U, 480U, 48U, 632U, 501U, 
    857U, 666U, 532U, 2226U, 1958U, 2158U, 1936U, 2130U, 
    1951U, 2110U, 2120U, 1371U, 1523U, 2302U, 1332U, 2032U, 
    803U, 1278U, 1912U, 1636U, 2331U, 2290U, 1580U, 1698U, 
    1706U, 1515U, 2057U, 2075U, 311U, 158U, 708U, 1747U, 
    1380U, 1729U, 579U, 453U, 1389U, 1500U, 1463U, 1054U, 
    1779U, 1490U, 1809U, 1680U, 1852U, 1398U, 428U, 264U, 
    374U, 215U, 1842U, 1472U, 1713U, 2341U, 2200U, 1892U, 
    2217U, 1905U, 1316U, 1965U, 1974U, 1155U, 1000U, 982U, 
    1104U, 643U, 511U, 863U, 677U, 542U, 2235U, 2093U, 
    2182U, 1871U, 1407U, 1626U, 1758U, 1645U, 1590U, 1918U, 
    1202U, 1173U, 1183U, 1163U, 2049U, 1721U, 2350U, 
};

static inline void InitXCoreMCInstrInfo(MCInstrInfo *II) {
  II->InitMCInstrInfo(XCoreInsts, XCoreInstrNameIndices, XCoreInstrNameData, 247);
}

} // End llvm namespace 
#endif // GET_INSTRINFO_MC_DESC


#ifdef GET_INSTRINFO_HEADER
#undef GET_INSTRINFO_HEADER
namespace llvm {
struct XCoreGenInstrInfo : public TargetInstrInfo {
  explicit XCoreGenInstrInfo(int SO = -1, int DO = -1);
  virtual ~XCoreGenInstrInfo();
};
} // End llvm namespace 
#endif // GET_INSTRINFO_HEADER


#ifdef GET_INSTRINFO_CTOR_DTOR
#undef GET_INSTRINFO_CTOR_DTOR
namespace llvm {
extern const MCInstrDesc XCoreInsts[];
extern const unsigned XCoreInstrNameIndices[];
extern const char XCoreInstrNameData[];
XCoreGenInstrInfo::XCoreGenInstrInfo(int SO, int DO)
  : TargetInstrInfo(SO, DO) {
  InitMCInstrInfo(XCoreInsts, XCoreInstrNameIndices, XCoreInstrNameData, 247);
}
XCoreGenInstrInfo::~XCoreGenInstrInfo() {}
} // End llvm namespace 
#endif // GET_INSTRINFO_CTOR_DTOR

#ifdef GET_INSTRINFO_OPERAND_ENUM
#undef GET_INSTRINFO_OPERAND_ENUM
namespace llvm {namespace XCore {
namespace OpName { 
enum {
OPERAND_LAST
};
} // End namespace OpName
} // End namespace XCore
} // End namespace llvm
#endif //GET_INSTRINFO_OPERAND_ENUM
#ifdef GET_INSTRINFO_NAMED_OPS
#undef GET_INSTRINFO_NAMED_OPS
namespace llvm {namespace XCore {
LLVM_READONLY
int16_t getNamedOperandIdx(uint16_t Opcode, uint16_t NamedIdx) {
  return -1;
}
} // End namespace XCore
} // End namespace llvm
#endif //GET_INSTRINFO_NAMED_OPS

#ifdef GET_INSTRINFO_OPERAND_TYPES_ENUM
#undef GET_INSTRINFO_OPERAND_TYPES_ENUM
namespace llvm {namespace XCore {
namespace OpTypes { 
enum OperandType {
  InlineJT = 0,
  InlineJT32 = 1,
  MEMii = 2,
  brtarget = 3,
  brtarget_neg = 4,
  f32imm = 5,
  f64imm = 6,
  i16imm = 7,
  i1imm = 8,
  i32imm = 9,
  i64imm = 10,
  i8imm = 11,
  pcrel_imm = 12,
  pcrel_imm_neg = 13,
  OPERAND_TYPE_LIST_END
};
} // End namespace OpTypes
} // End namespace XCore
} // End namespace llvm
#endif // GET_INSTRINFO_OPERAND_TYPES_ENUM
