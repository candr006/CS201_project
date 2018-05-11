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

namespace Mips {
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
    ABSQ_S_PH	= 22,
    ABSQ_S_QB	= 23,
    ABSQ_S_W	= 24,
    ADD	= 25,
    ADDIUPC	= 26,
    ADDIUR1SP_MM	= 27,
    ADDIUR2_MM	= 28,
    ADDIUS5_MM	= 29,
    ADDIUSP_MM	= 30,
    ADDQH_PH	= 31,
    ADDQH_R_PH	= 32,
    ADDQH_R_W	= 33,
    ADDQH_W	= 34,
    ADDQ_PH	= 35,
    ADDQ_S_PH	= 36,
    ADDQ_S_W	= 37,
    ADDSC	= 38,
    ADDS_A_B	= 39,
    ADDS_A_D	= 40,
    ADDS_A_H	= 41,
    ADDS_A_W	= 42,
    ADDS_S_B	= 43,
    ADDS_S_D	= 44,
    ADDS_S_H	= 45,
    ADDS_S_W	= 46,
    ADDS_U_B	= 47,
    ADDS_U_D	= 48,
    ADDS_U_H	= 49,
    ADDS_U_W	= 50,
    ADDU16_MM	= 51,
    ADDUH_QB	= 52,
    ADDUH_R_QB	= 53,
    ADDU_PH	= 54,
    ADDU_QB	= 55,
    ADDU_S_PH	= 56,
    ADDU_S_QB	= 57,
    ADDVI_B	= 58,
    ADDVI_D	= 59,
    ADDVI_H	= 60,
    ADDVI_W	= 61,
    ADDV_B	= 62,
    ADDV_D	= 63,
    ADDV_H	= 64,
    ADDV_W	= 65,
    ADDWC	= 66,
    ADD_A_B	= 67,
    ADD_A_D	= 68,
    ADD_A_H	= 69,
    ADD_A_W	= 70,
    ADD_MM	= 71,
    ADDi	= 72,
    ADDi_MM	= 73,
    ADDiu	= 74,
    ADDiu_MM	= 75,
    ADDu	= 76,
    ADDu_MM	= 77,
    ADJCALLSTACKDOWN	= 78,
    ADJCALLSTACKUP	= 79,
    ALIGN	= 80,
    ALUIPC	= 81,
    AND	= 82,
    AND16_MM	= 83,
    AND64	= 84,
    ANDI16_MM	= 85,
    ANDI_B	= 86,
    AND_MM	= 87,
    AND_V	= 88,
    AND_V_D_PSEUDO	= 89,
    AND_V_H_PSEUDO	= 90,
    AND_V_W_PSEUDO	= 91,
    ANDi	= 92,
    ANDi64	= 93,
    ANDi_MM	= 94,
    APPEND	= 95,
    ASUB_S_B	= 96,
    ASUB_S_D	= 97,
    ASUB_S_H	= 98,
    ASUB_S_W	= 99,
    ASUB_U_B	= 100,
    ASUB_U_D	= 101,
    ASUB_U_H	= 102,
    ASUB_U_W	= 103,
    ATOMIC_CMP_SWAP_I16	= 104,
    ATOMIC_CMP_SWAP_I32	= 105,
    ATOMIC_CMP_SWAP_I64	= 106,
    ATOMIC_CMP_SWAP_I8	= 107,
    ATOMIC_LOAD_ADD_I16	= 108,
    ATOMIC_LOAD_ADD_I32	= 109,
    ATOMIC_LOAD_ADD_I64	= 110,
    ATOMIC_LOAD_ADD_I8	= 111,
    ATOMIC_LOAD_AND_I16	= 112,
    ATOMIC_LOAD_AND_I32	= 113,
    ATOMIC_LOAD_AND_I64	= 114,
    ATOMIC_LOAD_AND_I8	= 115,
    ATOMIC_LOAD_NAND_I16	= 116,
    ATOMIC_LOAD_NAND_I32	= 117,
    ATOMIC_LOAD_NAND_I64	= 118,
    ATOMIC_LOAD_NAND_I8	= 119,
    ATOMIC_LOAD_OR_I16	= 120,
    ATOMIC_LOAD_OR_I32	= 121,
    ATOMIC_LOAD_OR_I64	= 122,
    ATOMIC_LOAD_OR_I8	= 123,
    ATOMIC_LOAD_SUB_I16	= 124,
    ATOMIC_LOAD_SUB_I32	= 125,
    ATOMIC_LOAD_SUB_I64	= 126,
    ATOMIC_LOAD_SUB_I8	= 127,
    ATOMIC_LOAD_XOR_I16	= 128,
    ATOMIC_LOAD_XOR_I32	= 129,
    ATOMIC_LOAD_XOR_I64	= 130,
    ATOMIC_LOAD_XOR_I8	= 131,
    ATOMIC_SWAP_I16	= 132,
    ATOMIC_SWAP_I32	= 133,
    ATOMIC_SWAP_I64	= 134,
    ATOMIC_SWAP_I8	= 135,
    AUI	= 136,
    AUIPC	= 137,
    AVER_S_B	= 138,
    AVER_S_D	= 139,
    AVER_S_H	= 140,
    AVER_S_W	= 141,
    AVER_U_B	= 142,
    AVER_U_D	= 143,
    AVER_U_H	= 144,
    AVER_U_W	= 145,
    AVE_S_B	= 146,
    AVE_S_D	= 147,
    AVE_S_H	= 148,
    AVE_S_W	= 149,
    AVE_U_B	= 150,
    AVE_U_D	= 151,
    AVE_U_H	= 152,
    AVE_U_W	= 153,
    AddiuRxImmX16	= 154,
    AddiuRxPcImmX16	= 155,
    AddiuRxRxImm16	= 156,
    AddiuRxRxImmX16	= 157,
    AddiuRxRyOffMemX16	= 158,
    AddiuSpImm16	= 159,
    AddiuSpImmX16	= 160,
    AdduRxRyRz16	= 161,
    AndRxRxRy16	= 162,
    B	= 163,
    BADDu	= 164,
    BAL	= 165,
    BALC	= 166,
    BALIGN	= 167,
    BAL_BR	= 168,
    BC	= 169,
    BC1EQZ	= 170,
    BC1F	= 171,
    BC1FL	= 172,
    BC1F_MM	= 173,
    BC1NEZ	= 174,
    BC1T	= 175,
    BC1TL	= 176,
    BC1T_MM	= 177,
    BC2EQZ	= 178,
    BC2NEZ	= 179,
    BCLRI_B	= 180,
    BCLRI_D	= 181,
    BCLRI_H	= 182,
    BCLRI_W	= 183,
    BCLR_B	= 184,
    BCLR_D	= 185,
    BCLR_H	= 186,
    BCLR_W	= 187,
    BEQ	= 188,
    BEQ64	= 189,
    BEQC	= 190,
    BEQL	= 191,
    BEQZ16_MM	= 192,
    BEQZALC	= 193,
    BEQZC	= 194,
    BEQZC_MM	= 195,
    BEQ_MM	= 196,
    BGEC	= 197,
    BGEUC	= 198,
    BGEZ	= 199,
    BGEZ64	= 200,
    BGEZAL	= 201,
    BGEZALC	= 202,
    BGEZALL	= 203,
    BGEZALS_MM	= 204,
    BGEZAL_MM	= 205,
    BGEZC	= 206,
    BGEZL	= 207,
    BGEZ_MM	= 208,
    BGTZ	= 209,
    BGTZ64	= 210,
    BGTZALC	= 211,
    BGTZC	= 212,
    BGTZL	= 213,
    BGTZ_MM	= 214,
    BINSLI_B	= 215,
    BINSLI_D	= 216,
    BINSLI_H	= 217,
    BINSLI_W	= 218,
    BINSL_B	= 219,
    BINSL_D	= 220,
    BINSL_H	= 221,
    BINSL_W	= 222,
    BINSRI_B	= 223,
    BINSRI_D	= 224,
    BINSRI_H	= 225,
    BINSRI_W	= 226,
    BINSR_B	= 227,
    BINSR_D	= 228,
    BINSR_H	= 229,
    BINSR_W	= 230,
    BITREV	= 231,
    BITSWAP	= 232,
    BLEZ	= 233,
    BLEZ64	= 234,
    BLEZALC	= 235,
    BLEZC	= 236,
    BLEZL	= 237,
    BLEZ_MM	= 238,
    BLTC	= 239,
    BLTUC	= 240,
    BLTZ	= 241,
    BLTZ64	= 242,
    BLTZAL	= 243,
    BLTZALC	= 244,
    BLTZALL	= 245,
    BLTZALS_MM	= 246,
    BLTZAL_MM	= 247,
    BLTZC	= 248,
    BLTZL	= 249,
    BLTZ_MM	= 250,
    BMNZI_B	= 251,
    BMNZ_V	= 252,
    BMZI_B	= 253,
    BMZ_V	= 254,
    BNE	= 255,
    BNE64	= 256,
    BNEC	= 257,
    BNEGI_B	= 258,
    BNEGI_D	= 259,
    BNEGI_H	= 260,
    BNEGI_W	= 261,
    BNEG_B	= 262,
    BNEG_D	= 263,
    BNEG_H	= 264,
    BNEG_W	= 265,
    BNEL	= 266,
    BNEZ16_MM	= 267,
    BNEZALC	= 268,
    BNEZC	= 269,
    BNEZC_MM	= 270,
    BNE_MM	= 271,
    BNVC	= 272,
    BNZ_B	= 273,
    BNZ_D	= 274,
    BNZ_H	= 275,
    BNZ_V	= 276,
    BNZ_W	= 277,
    BOVC	= 278,
    BPOSGE32	= 279,
    BPOSGE32_PSEUDO	= 280,
    BREAK	= 281,
    BREAK16_MM	= 282,
    BREAK_MM	= 283,
    BSELI_B	= 284,
    BSEL_D_PSEUDO	= 285,
    BSEL_FD_PSEUDO	= 286,
    BSEL_FW_PSEUDO	= 287,
    BSEL_H_PSEUDO	= 288,
    BSEL_V	= 289,
    BSEL_W_PSEUDO	= 290,
    BSETI_B	= 291,
    BSETI_D	= 292,
    BSETI_H	= 293,
    BSETI_W	= 294,
    BSET_B	= 295,
    BSET_D	= 296,
    BSET_H	= 297,
    BSET_W	= 298,
    BZ_B	= 299,
    BZ_D	= 300,
    BZ_H	= 301,
    BZ_V	= 302,
    BZ_W	= 303,
    BeqzRxImm16	= 304,
    BeqzRxImmX16	= 305,
    Bimm16	= 306,
    BimmX16	= 307,
    BnezRxImm16	= 308,
    BnezRxImmX16	= 309,
    Break16	= 310,
    Bteqz16	= 311,
    BteqzT8CmpX16	= 312,
    BteqzT8CmpiX16	= 313,
    BteqzT8SltX16	= 314,
    BteqzT8SltiX16	= 315,
    BteqzT8SltiuX16	= 316,
    BteqzT8SltuX16	= 317,
    BteqzX16	= 318,
    Btnez16	= 319,
    BtnezT8CmpX16	= 320,
    BtnezT8CmpiX16	= 321,
    BtnezT8SltX16	= 322,
    BtnezT8SltiX16	= 323,
    BtnezT8SltiuX16	= 324,
    BtnezT8SltuX16	= 325,
    BtnezX16	= 326,
    BuildPairF64	= 327,
    BuildPairF64_64	= 328,
    CACHE	= 329,
    CACHE_MM	= 330,
    CACHE_R6	= 331,
    CEIL_L_D64	= 332,
    CEIL_L_S	= 333,
    CEIL_W_D32	= 334,
    CEIL_W_D64	= 335,
    CEIL_W_MM	= 336,
    CEIL_W_S	= 337,
    CEIL_W_S_MM	= 338,
    CEQI_B	= 339,
    CEQI_D	= 340,
    CEQI_H	= 341,
    CEQI_W	= 342,
    CEQ_B	= 343,
    CEQ_D	= 344,
    CEQ_H	= 345,
    CEQ_W	= 346,
    CFC1	= 347,
    CFC1_MM	= 348,
    CFCMSA	= 349,
    CINS	= 350,
    CINS32	= 351,
    CLASS_D	= 352,
    CLASS_S	= 353,
    CLEI_S_B	= 354,
    CLEI_S_D	= 355,
    CLEI_S_H	= 356,
    CLEI_S_W	= 357,
    CLEI_U_B	= 358,
    CLEI_U_D	= 359,
    CLEI_U_H	= 360,
    CLEI_U_W	= 361,
    CLE_S_B	= 362,
    CLE_S_D	= 363,
    CLE_S_H	= 364,
    CLE_S_W	= 365,
    CLE_U_B	= 366,
    CLE_U_D	= 367,
    CLE_U_H	= 368,
    CLE_U_W	= 369,
    CLO	= 370,
    CLO_MM	= 371,
    CLO_R6	= 372,
    CLTI_S_B	= 373,
    CLTI_S_D	= 374,
    CLTI_S_H	= 375,
    CLTI_S_W	= 376,
    CLTI_U_B	= 377,
    CLTI_U_D	= 378,
    CLTI_U_H	= 379,
    CLTI_U_W	= 380,
    CLT_S_B	= 381,
    CLT_S_D	= 382,
    CLT_S_H	= 383,
    CLT_S_W	= 384,
    CLT_U_B	= 385,
    CLT_U_D	= 386,
    CLT_U_H	= 387,
    CLT_U_W	= 388,
    CLZ	= 389,
    CLZ_MM	= 390,
    CLZ_R6	= 391,
    CMPGDU_EQ_QB	= 392,
    CMPGDU_LE_QB	= 393,
    CMPGDU_LT_QB	= 394,
    CMPGU_EQ_QB	= 395,
    CMPGU_LE_QB	= 396,
    CMPGU_LT_QB	= 397,
    CMPU_EQ_QB	= 398,
    CMPU_LE_QB	= 399,
    CMPU_LT_QB	= 400,
    CMP_EQ_D	= 401,
    CMP_EQ_PH	= 402,
    CMP_EQ_S	= 403,
    CMP_F_D	= 404,
    CMP_F_S	= 405,
    CMP_LE_D	= 406,
    CMP_LE_PH	= 407,
    CMP_LE_S	= 408,
    CMP_LT_D	= 409,
    CMP_LT_PH	= 410,
    CMP_LT_S	= 411,
    CMP_SAF_D	= 412,
    CMP_SAF_S	= 413,
    CMP_SEQ_D	= 414,
    CMP_SEQ_S	= 415,
    CMP_SLE_D	= 416,
    CMP_SLE_S	= 417,
    CMP_SLT_D	= 418,
    CMP_SLT_S	= 419,
    CMP_SUEQ_D	= 420,
    CMP_SUEQ_S	= 421,
    CMP_SULE_D	= 422,
    CMP_SULE_S	= 423,
    CMP_SULT_D	= 424,
    CMP_SULT_S	= 425,
    CMP_SUN_D	= 426,
    CMP_SUN_S	= 427,
    CMP_UEQ_D	= 428,
    CMP_UEQ_S	= 429,
    CMP_ULE_D	= 430,
    CMP_ULE_S	= 431,
    CMP_ULT_D	= 432,
    CMP_ULT_S	= 433,
    CMP_UN_D	= 434,
    CMP_UN_S	= 435,
    CONSTPOOL_ENTRY	= 436,
    COPY_FD_PSEUDO	= 437,
    COPY_FW_PSEUDO	= 438,
    COPY_S_B	= 439,
    COPY_S_D	= 440,
    COPY_S_H	= 441,
    COPY_S_W	= 442,
    COPY_U_B	= 443,
    COPY_U_D	= 444,
    COPY_U_H	= 445,
    COPY_U_W	= 446,
    CTC1	= 447,
    CTC1_MM	= 448,
    CTCMSA	= 449,
    CVT_D32_S	= 450,
    CVT_D32_W	= 451,
    CVT_D32_W_MM	= 452,
    CVT_D64_L	= 453,
    CVT_D64_S	= 454,
    CVT_D64_W	= 455,
    CVT_D_S_MM	= 456,
    CVT_L_D64	= 457,
    CVT_L_D64_MM	= 458,
    CVT_L_S	= 459,
    CVT_L_S_MM	= 460,
    CVT_S_D32	= 461,
    CVT_S_D32_MM	= 462,
    CVT_S_D64	= 463,
    CVT_S_L	= 464,
    CVT_S_W	= 465,
    CVT_S_W_MM	= 466,
    CVT_W_D32	= 467,
    CVT_W_D64	= 468,
    CVT_W_MM	= 469,
    CVT_W_S	= 470,
    CVT_W_S_MM	= 471,
    C_EQ_D32	= 472,
    C_EQ_D64	= 473,
    C_EQ_S	= 474,
    C_F_D32	= 475,
    C_F_D64	= 476,
    C_F_S	= 477,
    C_LE_D32	= 478,
    C_LE_D64	= 479,
    C_LE_S	= 480,
    C_LT_D32	= 481,
    C_LT_D64	= 482,
    C_LT_S	= 483,
    C_NGE_D32	= 484,
    C_NGE_D64	= 485,
    C_NGE_S	= 486,
    C_NGLE_D32	= 487,
    C_NGLE_D64	= 488,
    C_NGLE_S	= 489,
    C_NGL_D32	= 490,
    C_NGL_D64	= 491,
    C_NGL_S	= 492,
    C_NGT_D32	= 493,
    C_NGT_D64	= 494,
    C_NGT_S	= 495,
    C_OLE_D32	= 496,
    C_OLE_D64	= 497,
    C_OLE_S	= 498,
    C_OLT_D32	= 499,
    C_OLT_D64	= 500,
    C_OLT_S	= 501,
    C_SEQ_D32	= 502,
    C_SEQ_D64	= 503,
    C_SEQ_S	= 504,
    C_SF_D32	= 505,
    C_SF_D64	= 506,
    C_SF_S	= 507,
    C_UEQ_D32	= 508,
    C_UEQ_D64	= 509,
    C_UEQ_S	= 510,
    C_ULE_D32	= 511,
    C_ULE_D64	= 512,
    C_ULE_S	= 513,
    C_ULT_D32	= 514,
    C_ULT_D64	= 515,
    C_ULT_S	= 516,
    C_UN_D32	= 517,
    C_UN_D64	= 518,
    C_UN_S	= 519,
    CmpRxRy16	= 520,
    CmpiRxImm16	= 521,
    CmpiRxImmX16	= 522,
    Constant32	= 523,
    DADD	= 524,
    DADDi	= 525,
    DADDiu	= 526,
    DADDu	= 527,
    DAHI	= 528,
    DALIGN	= 529,
    DATI	= 530,
    DAUI	= 531,
    DBITSWAP	= 532,
    DCLO	= 533,
    DCLO_R6	= 534,
    DCLZ	= 535,
    DCLZ_R6	= 536,
    DDIV	= 537,
    DDIVU	= 538,
    DERET	= 539,
    DERET_MM	= 540,
    DEXT	= 541,
    DEXTM	= 542,
    DEXTU	= 543,
    DI	= 544,
    DINS	= 545,
    DINSM	= 546,
    DINSU	= 547,
    DIV	= 548,
    DIVU	= 549,
    DIV_S_B	= 550,
    DIV_S_D	= 551,
    DIV_S_H	= 552,
    DIV_S_W	= 553,
    DIV_U_B	= 554,
    DIV_U_D	= 555,
    DIV_U_H	= 556,
    DIV_U_W	= 557,
    DI_MM	= 558,
    DLSA	= 559,
    DLSA_R6	= 560,
    DMFC0	= 561,
    DMFC1	= 562,
    DMFC2	= 563,
    DMOD	= 564,
    DMODU	= 565,
    DMTC0	= 566,
    DMTC1	= 567,
    DMTC2	= 568,
    DMUH	= 569,
    DMUHU	= 570,
    DMUL	= 571,
    DMULT	= 572,
    DMULTu	= 573,
    DMULU	= 574,
    DMUL_R6	= 575,
    DOTP_S_D	= 576,
    DOTP_S_H	= 577,
    DOTP_S_W	= 578,
    DOTP_U_D	= 579,
    DOTP_U_H	= 580,
    DOTP_U_W	= 581,
    DPADD_S_D	= 582,
    DPADD_S_H	= 583,
    DPADD_S_W	= 584,
    DPADD_U_D	= 585,
    DPADD_U_H	= 586,
    DPADD_U_W	= 587,
    DPAQX_SA_W_PH	= 588,
    DPAQX_S_W_PH	= 589,
    DPAQ_SA_L_W	= 590,
    DPAQ_S_W_PH	= 591,
    DPAU_H_QBL	= 592,
    DPAU_H_QBR	= 593,
    DPAX_W_PH	= 594,
    DPA_W_PH	= 595,
    DPOP	= 596,
    DPSQX_SA_W_PH	= 597,
    DPSQX_S_W_PH	= 598,
    DPSQ_SA_L_W	= 599,
    DPSQ_S_W_PH	= 600,
    DPSUB_S_D	= 601,
    DPSUB_S_H	= 602,
    DPSUB_S_W	= 603,
    DPSUB_U_D	= 604,
    DPSUB_U_H	= 605,
    DPSUB_U_W	= 606,
    DPSU_H_QBL	= 607,
    DPSU_H_QBR	= 608,
    DPSX_W_PH	= 609,
    DPS_W_PH	= 610,
    DROTR	= 611,
    DROTR32	= 612,
    DROTRV	= 613,
    DSBH	= 614,
    DSDIV	= 615,
    DSHD	= 616,
    DSLL	= 617,
    DSLL32	= 618,
    DSLL64_32	= 619,
    DSLLV	= 620,
    DSRA	= 621,
    DSRA32	= 622,
    DSRAV	= 623,
    DSRL	= 624,
    DSRL32	= 625,
    DSRLV	= 626,
    DSUB	= 627,
    DSUBu	= 628,
    DUDIV	= 629,
    DivRxRy16	= 630,
    DivuRxRy16	= 631,
    EHB	= 632,
    EHB_MM	= 633,
    EI	= 634,
    EI_MM	= 635,
    ERET	= 636,
    ERET_MM	= 637,
    EXT	= 638,
    EXTP	= 639,
    EXTPDP	= 640,
    EXTPDPV	= 641,
    EXTPV	= 642,
    EXTRV_RS_W	= 643,
    EXTRV_R_W	= 644,
    EXTRV_S_H	= 645,
    EXTRV_W	= 646,
    EXTR_RS_W	= 647,
    EXTR_R_W	= 648,
    EXTR_S_H	= 649,
    EXTR_W	= 650,
    EXTS	= 651,
    EXTS32	= 652,
    EXT_MM	= 653,
    ExtractElementF64	= 654,
    ExtractElementF64_64	= 655,
    FABS_D	= 656,
    FABS_D32	= 657,
    FABS_D64	= 658,
    FABS_MM	= 659,
    FABS_S	= 660,
    FABS_S_MM	= 661,
    FABS_W	= 662,
    FADD_D	= 663,
    FADD_D32	= 664,
    FADD_D64	= 665,
    FADD_MM	= 666,
    FADD_S	= 667,
    FADD_S_MM	= 668,
    FADD_W	= 669,
    FCAF_D	= 670,
    FCAF_W	= 671,
    FCEQ_D	= 672,
    FCEQ_W	= 673,
    FCLASS_D	= 674,
    FCLASS_W	= 675,
    FCLE_D	= 676,
    FCLE_W	= 677,
    FCLT_D	= 678,
    FCLT_W	= 679,
    FCMP_D32	= 680,
    FCMP_D32_MM	= 681,
    FCMP_D64	= 682,
    FCMP_S32	= 683,
    FCMP_S32_MM	= 684,
    FCNE_D	= 685,
    FCNE_W	= 686,
    FCOR_D	= 687,
    FCOR_W	= 688,
    FCUEQ_D	= 689,
    FCUEQ_W	= 690,
    FCULE_D	= 691,
    FCULE_W	= 692,
    FCULT_D	= 693,
    FCULT_W	= 694,
    FCUNE_D	= 695,
    FCUNE_W	= 696,
    FCUN_D	= 697,
    FCUN_W	= 698,
    FDIV_D	= 699,
    FDIV_D32	= 700,
    FDIV_D64	= 701,
    FDIV_MM	= 702,
    FDIV_S	= 703,
    FDIV_S_MM	= 704,
    FDIV_W	= 705,
    FEXDO_H	= 706,
    FEXDO_W	= 707,
    FEXP2_D	= 708,
    FEXP2_D_1_PSEUDO	= 709,
    FEXP2_W	= 710,
    FEXP2_W_1_PSEUDO	= 711,
    FEXUPL_D	= 712,
    FEXUPL_W	= 713,
    FEXUPR_D	= 714,
    FEXUPR_W	= 715,
    FFINT_S_D	= 716,
    FFINT_S_W	= 717,
    FFINT_U_D	= 718,
    FFINT_U_W	= 719,
    FFQL_D	= 720,
    FFQL_W	= 721,
    FFQR_D	= 722,
    FFQR_W	= 723,
    FILL_B	= 724,
    FILL_D	= 725,
    FILL_FD_PSEUDO	= 726,
    FILL_FW_PSEUDO	= 727,
    FILL_H	= 728,
    FILL_W	= 729,
    FLOG2_D	= 730,
    FLOG2_W	= 731,
    FLOOR_L_D64	= 732,
    FLOOR_L_S	= 733,
    FLOOR_W_D32	= 734,
    FLOOR_W_D64	= 735,
    FLOOR_W_MM	= 736,
    FLOOR_W_S	= 737,
    FLOOR_W_S_MM	= 738,
    FMADD_D	= 739,
    FMADD_W	= 740,
    FMAX_A_D	= 741,
    FMAX_A_W	= 742,
    FMAX_D	= 743,
    FMAX_W	= 744,
    FMIN_A_D	= 745,
    FMIN_A_W	= 746,
    FMIN_D	= 747,
    FMIN_W	= 748,
    FMOV_D32	= 749,
    FMOV_D32_MM	= 750,
    FMOV_D64	= 751,
    FMOV_S	= 752,
    FMOV_S_MM	= 753,
    FMSUB_D	= 754,
    FMSUB_W	= 755,
    FMUL_D	= 756,
    FMUL_D32	= 757,
    FMUL_D64	= 758,
    FMUL_MM	= 759,
    FMUL_S	= 760,
    FMUL_S_MM	= 761,
    FMUL_W	= 762,
    FNEG_D32	= 763,
    FNEG_D64	= 764,
    FNEG_MM	= 765,
    FNEG_S	= 766,
    FNEG_S_MM	= 767,
    FRCP_D	= 768,
    FRCP_W	= 769,
    FRINT_D	= 770,
    FRINT_W	= 771,
    FRSQRT_D	= 772,
    FRSQRT_W	= 773,
    FSAF_D	= 774,
    FSAF_W	= 775,
    FSEQ_D	= 776,
    FSEQ_W	= 777,
    FSLE_D	= 778,
    FSLE_W	= 779,
    FSLT_D	= 780,
    FSLT_W	= 781,
    FSNE_D	= 782,
    FSNE_W	= 783,
    FSOR_D	= 784,
    FSOR_W	= 785,
    FSQRT_D	= 786,
    FSQRT_D32	= 787,
    FSQRT_D64	= 788,
    FSQRT_MM	= 789,
    FSQRT_S	= 790,
    FSQRT_S_MM	= 791,
    FSQRT_W	= 792,
    FSUB_D	= 793,
    FSUB_D32	= 794,
    FSUB_D64	= 795,
    FSUB_MM	= 796,
    FSUB_S	= 797,
    FSUB_S_MM	= 798,
    FSUB_W	= 799,
    FSUEQ_D	= 800,
    FSUEQ_W	= 801,
    FSULE_D	= 802,
    FSULE_W	= 803,
    FSULT_D	= 804,
    FSULT_W	= 805,
    FSUNE_D	= 806,
    FSUNE_W	= 807,
    FSUN_D	= 808,
    FSUN_W	= 809,
    FTINT_S_D	= 810,
    FTINT_S_W	= 811,
    FTINT_U_D	= 812,
    FTINT_U_W	= 813,
    FTQ_H	= 814,
    FTQ_W	= 815,
    FTRUNC_S_D	= 816,
    FTRUNC_S_W	= 817,
    FTRUNC_U_D	= 818,
    FTRUNC_U_W	= 819,
    GotPrologue16	= 820,
    HADD_S_D	= 821,
    HADD_S_H	= 822,
    HADD_S_W	= 823,
    HADD_U_D	= 824,
    HADD_U_H	= 825,
    HADD_U_W	= 826,
    HSUB_S_D	= 827,
    HSUB_S_H	= 828,
    HSUB_S_W	= 829,
    HSUB_U_D	= 830,
    HSUB_U_H	= 831,
    HSUB_U_W	= 832,
    ILVEV_B	= 833,
    ILVEV_D	= 834,
    ILVEV_H	= 835,
    ILVEV_W	= 836,
    ILVL_B	= 837,
    ILVL_D	= 838,
    ILVL_H	= 839,
    ILVL_W	= 840,
    ILVOD_B	= 841,
    ILVOD_D	= 842,
    ILVOD_H	= 843,
    ILVOD_W	= 844,
    ILVR_B	= 845,
    ILVR_D	= 846,
    ILVR_H	= 847,
    ILVR_W	= 848,
    INS	= 849,
    INSERT_B	= 850,
    INSERT_B_VIDX_PSEUDO	= 851,
    INSERT_D	= 852,
    INSERT_D_VIDX_PSEUDO	= 853,
    INSERT_FD_PSEUDO	= 854,
    INSERT_FD_VIDX_PSEUDO	= 855,
    INSERT_FW_PSEUDO	= 856,
    INSERT_FW_VIDX_PSEUDO	= 857,
    INSERT_H	= 858,
    INSERT_H_VIDX_PSEUDO	= 859,
    INSERT_W	= 860,
    INSERT_W_VIDX_PSEUDO	= 861,
    INSV	= 862,
    INSVE_B	= 863,
    INSVE_D	= 864,
    INSVE_H	= 865,
    INSVE_W	= 866,
    INS_MM	= 867,
    J	= 868,
    JAL	= 869,
    JALR	= 870,
    JALR16_MM	= 871,
    JALR64	= 872,
    JALR64Pseudo	= 873,
    JALRPseudo	= 874,
    JALRS16_MM	= 875,
    JALRS_MM	= 876,
    JALR_HB	= 877,
    JALR_MM	= 878,
    JALS_MM	= 879,
    JALX	= 880,
    JAL_MM	= 881,
    JIALC	= 882,
    JIC	= 883,
    JR	= 884,
    JR16_MM	= 885,
    JR64	= 886,
    JRADDIUSP	= 887,
    JRC16_MM	= 888,
    JR_HB	= 889,
    JR_HB_R6	= 890,
    JR_MM	= 891,
    J_MM	= 892,
    Jal16	= 893,
    JalB16	= 894,
    JrRa16	= 895,
    JrcRa16	= 896,
    JrcRx16	= 897,
    JumpLinkReg16	= 898,
    LB	= 899,
    LB64	= 900,
    LBU16_MM	= 901,
    LBUX	= 902,
    LB_MM	= 903,
    LBu	= 904,
    LBu64	= 905,
    LBu_MM	= 906,
    LD	= 907,
    LDC1	= 908,
    LDC164	= 909,
    LDC1_MM	= 910,
    LDC2	= 911,
    LDC2_R6	= 912,
    LDC3	= 913,
    LDI_B	= 914,
    LDI_D	= 915,
    LDI_H	= 916,
    LDI_W	= 917,
    LDL	= 918,
    LDPC	= 919,
    LDR	= 920,
    LDXC1	= 921,
    LDXC164	= 922,
    LD_B	= 923,
    LD_D	= 924,
    LD_H	= 925,
    LD_W	= 926,
    LEA_ADDiu	= 927,
    LEA_ADDiu64	= 928,
    LEA_ADDiu_MM	= 929,
    LH	= 930,
    LH64	= 931,
    LHU16_MM	= 932,
    LHX	= 933,
    LH_MM	= 934,
    LHu	= 935,
    LHu64	= 936,
    LHu_MM	= 937,
    LI16_MM	= 938,
    LL	= 939,
    LLD	= 940,
    LLD_R6	= 941,
    LL_MM	= 942,
    LL_R6	= 943,
    LOAD_ACC128	= 944,
    LOAD_ACC64	= 945,
    LOAD_ACC64DSP	= 946,
    LOAD_CCOND_DSP	= 947,
    LONG_BRANCH_ADDiu	= 948,
    LONG_BRANCH_DADDiu	= 949,
    LONG_BRANCH_LUi	= 950,
    LSA	= 951,
    LSA_R6	= 952,
    LUXC1	= 953,
    LUXC164	= 954,
    LUXC1_MM	= 955,
    LUi	= 956,
    LUi64	= 957,
    LUi_MM	= 958,
    LW	= 959,
    LW16_MM	= 960,
    LW64	= 961,
    LWC1	= 962,
    LWC1_MM	= 963,
    LWC2	= 964,
    LWC2_R6	= 965,
    LWC3	= 966,
    LWL	= 967,
    LWL64	= 968,
    LWL_MM	= 969,
    LWM16_MM	= 970,
    LWM32_MM	= 971,
    LWPC	= 972,
    LWP_MM	= 973,
    LWR	= 974,
    LWR64	= 975,
    LWR_MM	= 976,
    LWSP_MM	= 977,
    LWUPC	= 978,
    LWU_MM	= 979,
    LWX	= 980,
    LWXC1	= 981,
    LWXC1_MM	= 982,
    LWXS_MM	= 983,
    LW_MM	= 984,
    LWu	= 985,
    LbRxRyOffMemX16	= 986,
    LbuRxRyOffMemX16	= 987,
    LhRxRyOffMemX16	= 988,
    LhuRxRyOffMemX16	= 989,
    LiRxImm16	= 990,
    LiRxImmAlignX16	= 991,
    LiRxImmX16	= 992,
    LoadAddr32Imm	= 993,
    LoadAddr32Reg	= 994,
    LoadImm32Reg	= 995,
    LoadImm64Reg	= 996,
    LwConstant32	= 997,
    LwRxPcTcp16	= 998,
    LwRxPcTcpX16	= 999,
    LwRxRyOffMemX16	= 1000,
    LwRxSpImmX16	= 1001,
    MADD	= 1002,
    MADDF_D	= 1003,
    MADDF_S	= 1004,
    MADDR_Q_H	= 1005,
    MADDR_Q_W	= 1006,
    MADDU	= 1007,
    MADDU_DSP	= 1008,
    MADDU_MM	= 1009,
    MADDV_B	= 1010,
    MADDV_D	= 1011,
    MADDV_H	= 1012,
    MADDV_W	= 1013,
    MADD_D32	= 1014,
    MADD_D32_MM	= 1015,
    MADD_D64	= 1016,
    MADD_DSP	= 1017,
    MADD_MM	= 1018,
    MADD_Q_H	= 1019,
    MADD_Q_W	= 1020,
    MADD_S	= 1021,
    MADD_S_MM	= 1022,
    MAQ_SA_W_PHL	= 1023,
    MAQ_SA_W_PHR	= 1024,
    MAQ_S_W_PHL	= 1025,
    MAQ_S_W_PHR	= 1026,
    MAXA_D	= 1027,
    MAXA_S	= 1028,
    MAXI_S_B	= 1029,
    MAXI_S_D	= 1030,
    MAXI_S_H	= 1031,
    MAXI_S_W	= 1032,
    MAXI_U_B	= 1033,
    MAXI_U_D	= 1034,
    MAXI_U_H	= 1035,
    MAXI_U_W	= 1036,
    MAX_A_B	= 1037,
    MAX_A_D	= 1038,
    MAX_A_H	= 1039,
    MAX_A_W	= 1040,
    MAX_D	= 1041,
    MAX_S	= 1042,
    MAX_S_B	= 1043,
    MAX_S_D	= 1044,
    MAX_S_H	= 1045,
    MAX_S_W	= 1046,
    MAX_U_B	= 1047,
    MAX_U_D	= 1048,
    MAX_U_H	= 1049,
    MAX_U_W	= 1050,
    MFC0	= 1051,
    MFC1	= 1052,
    MFC1_MM	= 1053,
    MFC2	= 1054,
    MFHC1_D32	= 1055,
    MFHC1_D64	= 1056,
    MFHC1_MM	= 1057,
    MFHI	= 1058,
    MFHI16_MM	= 1059,
    MFHI64	= 1060,
    MFHI_DSP	= 1061,
    MFHI_MM	= 1062,
    MFLO	= 1063,
    MFLO16_MM	= 1064,
    MFLO64	= 1065,
    MFLO_DSP	= 1066,
    MFLO_MM	= 1067,
    MINA_D	= 1068,
    MINA_S	= 1069,
    MINI_S_B	= 1070,
    MINI_S_D	= 1071,
    MINI_S_H	= 1072,
    MINI_S_W	= 1073,
    MINI_U_B	= 1074,
    MINI_U_D	= 1075,
    MINI_U_H	= 1076,
    MINI_U_W	= 1077,
    MIN_A_B	= 1078,
    MIN_A_D	= 1079,
    MIN_A_H	= 1080,
    MIN_A_W	= 1081,
    MIN_D	= 1082,
    MIN_S	= 1083,
    MIN_S_B	= 1084,
    MIN_S_D	= 1085,
    MIN_S_H	= 1086,
    MIN_S_W	= 1087,
    MIN_U_B	= 1088,
    MIN_U_D	= 1089,
    MIN_U_H	= 1090,
    MIN_U_W	= 1091,
    MIPSeh_return32	= 1092,
    MIPSeh_return64	= 1093,
    MOD	= 1094,
    MODSUB	= 1095,
    MODU	= 1096,
    MOD_S_B	= 1097,
    MOD_S_D	= 1098,
    MOD_S_H	= 1099,
    MOD_S_W	= 1100,
    MOD_U_B	= 1101,
    MOD_U_D	= 1102,
    MOD_U_H	= 1103,
    MOD_U_W	= 1104,
    MOVE16_MM	= 1105,
    MOVE_V	= 1106,
    MOVF_D32	= 1107,
    MOVF_D32_MM	= 1108,
    MOVF_D64	= 1109,
    MOVF_I	= 1110,
    MOVF_I64	= 1111,
    MOVF_I_MM	= 1112,
    MOVF_S	= 1113,
    MOVF_S_MM	= 1114,
    MOVN_I64_D64	= 1115,
    MOVN_I64_I	= 1116,
    MOVN_I64_I64	= 1117,
    MOVN_I64_S	= 1118,
    MOVN_I_D32	= 1119,
    MOVN_I_D32_MM	= 1120,
    MOVN_I_D64	= 1121,
    MOVN_I_I	= 1122,
    MOVN_I_I64	= 1123,
    MOVN_I_MM	= 1124,
    MOVN_I_S	= 1125,
    MOVN_I_S_MM	= 1126,
    MOVT_D32	= 1127,
    MOVT_D32_MM	= 1128,
    MOVT_D64	= 1129,
    MOVT_I	= 1130,
    MOVT_I64	= 1131,
    MOVT_I_MM	= 1132,
    MOVT_S	= 1133,
    MOVT_S_MM	= 1134,
    MOVZ_I64_D64	= 1135,
    MOVZ_I64_I	= 1136,
    MOVZ_I64_I64	= 1137,
    MOVZ_I64_S	= 1138,
    MOVZ_I_D32	= 1139,
    MOVZ_I_D32_MM	= 1140,
    MOVZ_I_D64	= 1141,
    MOVZ_I_I	= 1142,
    MOVZ_I_I64	= 1143,
    MOVZ_I_MM	= 1144,
    MOVZ_I_S	= 1145,
    MOVZ_I_S_MM	= 1146,
    MSUB	= 1147,
    MSUBF_D	= 1148,
    MSUBF_S	= 1149,
    MSUBR_Q_H	= 1150,
    MSUBR_Q_W	= 1151,
    MSUBU	= 1152,
    MSUBU_DSP	= 1153,
    MSUBU_MM	= 1154,
    MSUBV_B	= 1155,
    MSUBV_D	= 1156,
    MSUBV_H	= 1157,
    MSUBV_W	= 1158,
    MSUB_D32	= 1159,
    MSUB_D32_MM	= 1160,
    MSUB_D64	= 1161,
    MSUB_DSP	= 1162,
    MSUB_MM	= 1163,
    MSUB_Q_H	= 1164,
    MSUB_Q_W	= 1165,
    MSUB_S	= 1166,
    MSUB_S_MM	= 1167,
    MTC0	= 1168,
    MTC1	= 1169,
    MTC1_MM	= 1170,
    MTC2	= 1171,
    MTHC1_D32	= 1172,
    MTHC1_D64	= 1173,
    MTHC1_MM	= 1174,
    MTHI	= 1175,
    MTHI64	= 1176,
    MTHI_DSP	= 1177,
    MTHI_MM	= 1178,
    MTHLIP	= 1179,
    MTLO	= 1180,
    MTLO64	= 1181,
    MTLO_DSP	= 1182,
    MTLO_MM	= 1183,
    MTM0	= 1184,
    MTM1	= 1185,
    MTM2	= 1186,
    MTP0	= 1187,
    MTP1	= 1188,
    MTP2	= 1189,
    MUH	= 1190,
    MUHU	= 1191,
    MUL	= 1192,
    MULEQ_S_W_PHL	= 1193,
    MULEQ_S_W_PHR	= 1194,
    MULEU_S_PH_QBL	= 1195,
    MULEU_S_PH_QBR	= 1196,
    MULQ_RS_PH	= 1197,
    MULQ_RS_W	= 1198,
    MULQ_S_PH	= 1199,
    MULQ_S_W	= 1200,
    MULR_Q_H	= 1201,
    MULR_Q_W	= 1202,
    MULSAQ_S_W_PH	= 1203,
    MULSA_W_PH	= 1204,
    MULT	= 1205,
    MULTU_DSP	= 1206,
    MULT_DSP	= 1207,
    MULT_MM	= 1208,
    MULTu	= 1209,
    MULTu_MM	= 1210,
    MULU	= 1211,
    MULV_B	= 1212,
    MULV_D	= 1213,
    MULV_H	= 1214,
    MULV_W	= 1215,
    MUL_MM	= 1216,
    MUL_PH	= 1217,
    MUL_Q_H	= 1218,
    MUL_Q_W	= 1219,
    MUL_R6	= 1220,
    MUL_S_PH	= 1221,
    Mfhi16	= 1222,
    Mflo16	= 1223,
    Move32R16	= 1224,
    MoveR3216	= 1225,
    MultRxRy16	= 1226,
    MultRxRyRz16	= 1227,
    MultuRxRy16	= 1228,
    MultuRxRyRz16	= 1229,
    NLOC_B	= 1230,
    NLOC_D	= 1231,
    NLOC_H	= 1232,
    NLOC_W	= 1233,
    NLZC_B	= 1234,
    NLZC_D	= 1235,
    NLZC_H	= 1236,
    NLZC_W	= 1237,
    NMADD_D32	= 1238,
    NMADD_D32_MM	= 1239,
    NMADD_D64	= 1240,
    NMADD_S	= 1241,
    NMADD_S_MM	= 1242,
    NMSUB_D32	= 1243,
    NMSUB_D32_MM	= 1244,
    NMSUB_D64	= 1245,
    NMSUB_S	= 1246,
    NMSUB_S_MM	= 1247,
    NOP	= 1248,
    NOR	= 1249,
    NOR64	= 1250,
    NORI_B	= 1251,
    NOR_MM	= 1252,
    NOR_V	= 1253,
    NOR_V_D_PSEUDO	= 1254,
    NOR_V_H_PSEUDO	= 1255,
    NOR_V_W_PSEUDO	= 1256,
    NOT16_MM	= 1257,
    NegRxRy16	= 1258,
    NotRxRy16	= 1259,
    OR	= 1260,
    OR16_MM	= 1261,
    OR64	= 1262,
    ORI_B	= 1263,
    OR_MM	= 1264,
    OR_V	= 1265,
    OR_V_D_PSEUDO	= 1266,
    OR_V_H_PSEUDO	= 1267,
    OR_V_W_PSEUDO	= 1268,
    ORi	= 1269,
    ORi64	= 1270,
    ORi_MM	= 1271,
    OrRxRxRy16	= 1272,
    PACKRL_PH	= 1273,
    PAUSE	= 1274,
    PAUSE_MM	= 1275,
    PCKEV_B	= 1276,
    PCKEV_D	= 1277,
    PCKEV_H	= 1278,
    PCKEV_W	= 1279,
    PCKOD_B	= 1280,
    PCKOD_D	= 1281,
    PCKOD_H	= 1282,
    PCKOD_W	= 1283,
    PCNT_B	= 1284,
    PCNT_D	= 1285,
    PCNT_H	= 1286,
    PCNT_W	= 1287,
    PICK_PH	= 1288,
    PICK_QB	= 1289,
    POP	= 1290,
    PRECEQU_PH_QBL	= 1291,
    PRECEQU_PH_QBLA	= 1292,
    PRECEQU_PH_QBR	= 1293,
    PRECEQU_PH_QBRA	= 1294,
    PRECEQ_W_PHL	= 1295,
    PRECEQ_W_PHR	= 1296,
    PRECEU_PH_QBL	= 1297,
    PRECEU_PH_QBLA	= 1298,
    PRECEU_PH_QBR	= 1299,
    PRECEU_PH_QBRA	= 1300,
    PRECRQU_S_QB_PH	= 1301,
    PRECRQ_PH_W	= 1302,
    PRECRQ_QB_PH	= 1303,
    PRECRQ_RS_PH_W	= 1304,
    PRECR_QB_PH	= 1305,
    PRECR_SRA_PH_W	= 1306,
    PRECR_SRA_R_PH_W	= 1307,
    PREF	= 1308,
    PREF_MM	= 1309,
    PREF_R6	= 1310,
    PREPEND	= 1311,
    PseudoCMPU_EQ_QB	= 1312,
    PseudoCMPU_LE_QB	= 1313,
    PseudoCMPU_LT_QB	= 1314,
    PseudoCMP_EQ_PH	= 1315,
    PseudoCMP_LE_PH	= 1316,
    PseudoCMP_LT_PH	= 1317,
    PseudoCVT_D32_W	= 1318,
    PseudoCVT_D64_L	= 1319,
    PseudoCVT_D64_W	= 1320,
    PseudoCVT_S_L	= 1321,
    PseudoCVT_S_W	= 1322,
    PseudoDMULT	= 1323,
    PseudoDMULTu	= 1324,
    PseudoDSDIV	= 1325,
    PseudoDUDIV	= 1326,
    PseudoIndirectBranch	= 1327,
    PseudoIndirectBranch64	= 1328,
    PseudoMADD	= 1329,
    PseudoMADDU	= 1330,
    PseudoMFHI	= 1331,
    PseudoMFHI64	= 1332,
    PseudoMFLO	= 1333,
    PseudoMFLO64	= 1334,
    PseudoMSUB	= 1335,
    PseudoMSUBU	= 1336,
    PseudoMTLOHI	= 1337,
    PseudoMTLOHI64	= 1338,
    PseudoMTLOHI_DSP	= 1339,
    PseudoMULT	= 1340,
    PseudoMULTu	= 1341,
    PseudoPICK_PH	= 1342,
    PseudoPICK_QB	= 1343,
    PseudoReturn	= 1344,
    PseudoReturn64	= 1345,
    PseudoSDIV	= 1346,
    PseudoSELECTFP_F_D32	= 1347,
    PseudoSELECTFP_F_D64	= 1348,
    PseudoSELECTFP_F_I	= 1349,
    PseudoSELECTFP_F_I64	= 1350,
    PseudoSELECTFP_F_S	= 1351,
    PseudoSELECTFP_T_D32	= 1352,
    PseudoSELECTFP_T_D64	= 1353,
    PseudoSELECTFP_T_I	= 1354,
    PseudoSELECTFP_T_I64	= 1355,
    PseudoSELECTFP_T_S	= 1356,
    PseudoSELECT_D32	= 1357,
    PseudoSELECT_D64	= 1358,
    PseudoSELECT_I	= 1359,
    PseudoSELECT_I64	= 1360,
    PseudoSELECT_S	= 1361,
    PseudoUDIV	= 1362,
    RADDU_W_QB	= 1363,
    RDDSP	= 1364,
    RDHWR	= 1365,
    RDHWR64	= 1366,
    RDHWR_MM	= 1367,
    REPLV_PH	= 1368,
    REPLV_QB	= 1369,
    REPL_PH	= 1370,
    REPL_QB	= 1371,
    RINT_D	= 1372,
    RINT_S	= 1373,
    ROTR	= 1374,
    ROTRV	= 1375,
    ROTRV_MM	= 1376,
    ROTR_MM	= 1377,
    ROUND_L_D64	= 1378,
    ROUND_L_S	= 1379,
    ROUND_W_D32	= 1380,
    ROUND_W_D64	= 1381,
    ROUND_W_MM	= 1382,
    ROUND_W_S	= 1383,
    ROUND_W_S_MM	= 1384,
    Restore16	= 1385,
    RestoreX16	= 1386,
    RetRA	= 1387,
    RetRA16	= 1388,
    SAT_S_B	= 1389,
    SAT_S_D	= 1390,
    SAT_S_H	= 1391,
    SAT_S_W	= 1392,
    SAT_U_B	= 1393,
    SAT_U_D	= 1394,
    SAT_U_H	= 1395,
    SAT_U_W	= 1396,
    SB	= 1397,
    SB16_MM	= 1398,
    SB64	= 1399,
    SB_MM	= 1400,
    SC	= 1401,
    SCD	= 1402,
    SCD_R6	= 1403,
    SC_MM	= 1404,
    SC_R6	= 1405,
    SD	= 1406,
    SDBBP	= 1407,
    SDBBP16_MM	= 1408,
    SDBBP_MM	= 1409,
    SDBBP_R6	= 1410,
    SDC1	= 1411,
    SDC164	= 1412,
    SDC1_MM	= 1413,
    SDC2	= 1414,
    SDC2_R6	= 1415,
    SDC3	= 1416,
    SDIV	= 1417,
    SDIV_MM	= 1418,
    SDL	= 1419,
    SDR	= 1420,
    SDXC1	= 1421,
    SDXC164	= 1422,
    SEB	= 1423,
    SEB64	= 1424,
    SEB_MM	= 1425,
    SEH	= 1426,
    SEH64	= 1427,
    SEH_MM	= 1428,
    SELEQZ	= 1429,
    SELEQZ64	= 1430,
    SELEQZ_D	= 1431,
    SELEQZ_S	= 1432,
    SELNEZ	= 1433,
    SELNEZ64	= 1434,
    SELNEZ_D	= 1435,
    SELNEZ_S	= 1436,
    SEL_D	= 1437,
    SEL_S	= 1438,
    SEQ	= 1439,
    SEQi	= 1440,
    SH	= 1441,
    SH16_MM	= 1442,
    SH64	= 1443,
    SHF_B	= 1444,
    SHF_H	= 1445,
    SHF_W	= 1446,
    SHILO	= 1447,
    SHILOV	= 1448,
    SHLLV_PH	= 1449,
    SHLLV_QB	= 1450,
    SHLLV_S_PH	= 1451,
    SHLLV_S_W	= 1452,
    SHLL_PH	= 1453,
    SHLL_QB	= 1454,
    SHLL_S_PH	= 1455,
    SHLL_S_W	= 1456,
    SHRAV_PH	= 1457,
    SHRAV_QB	= 1458,
    SHRAV_R_PH	= 1459,
    SHRAV_R_QB	= 1460,
    SHRAV_R_W	= 1461,
    SHRA_PH	= 1462,
    SHRA_QB	= 1463,
    SHRA_R_PH	= 1464,
    SHRA_R_QB	= 1465,
    SHRA_R_W	= 1466,
    SHRLV_PH	= 1467,
    SHRLV_QB	= 1468,
    SHRL_PH	= 1469,
    SHRL_QB	= 1470,
    SH_MM	= 1471,
    SLDI_B	= 1472,
    SLDI_D	= 1473,
    SLDI_H	= 1474,
    SLDI_W	= 1475,
    SLD_B	= 1476,
    SLD_D	= 1477,
    SLD_H	= 1478,
    SLD_W	= 1479,
    SLL	= 1480,
    SLL16_MM	= 1481,
    SLL64_32	= 1482,
    SLL64_64	= 1483,
    SLLI_B	= 1484,
    SLLI_D	= 1485,
    SLLI_H	= 1486,
    SLLI_W	= 1487,
    SLLV	= 1488,
    SLLV_MM	= 1489,
    SLL_B	= 1490,
    SLL_D	= 1491,
    SLL_H	= 1492,
    SLL_MM	= 1493,
    SLL_W	= 1494,
    SLT	= 1495,
    SLT64	= 1496,
    SLT_MM	= 1497,
    SLTi	= 1498,
    SLTi64	= 1499,
    SLTi_MM	= 1500,
    SLTiu	= 1501,
    SLTiu64	= 1502,
    SLTiu_MM	= 1503,
    SLTu	= 1504,
    SLTu64	= 1505,
    SLTu_MM	= 1506,
    SNE	= 1507,
    SNEi	= 1508,
    SNZ_B_PSEUDO	= 1509,
    SNZ_D_PSEUDO	= 1510,
    SNZ_H_PSEUDO	= 1511,
    SNZ_V_PSEUDO	= 1512,
    SNZ_W_PSEUDO	= 1513,
    SPLATI_B	= 1514,
    SPLATI_D	= 1515,
    SPLATI_H	= 1516,
    SPLATI_W	= 1517,
    SPLAT_B	= 1518,
    SPLAT_D	= 1519,
    SPLAT_H	= 1520,
    SPLAT_W	= 1521,
    SRA	= 1522,
    SRAI_B	= 1523,
    SRAI_D	= 1524,
    SRAI_H	= 1525,
    SRAI_W	= 1526,
    SRARI_B	= 1527,
    SRARI_D	= 1528,
    SRARI_H	= 1529,
    SRARI_W	= 1530,
    SRAR_B	= 1531,
    SRAR_D	= 1532,
    SRAR_H	= 1533,
    SRAR_W	= 1534,
    SRAV	= 1535,
    SRAV_MM	= 1536,
    SRA_B	= 1537,
    SRA_D	= 1538,
    SRA_H	= 1539,
    SRA_MM	= 1540,
    SRA_W	= 1541,
    SRL	= 1542,
    SRL16_MM	= 1543,
    SRLI_B	= 1544,
    SRLI_D	= 1545,
    SRLI_H	= 1546,
    SRLI_W	= 1547,
    SRLRI_B	= 1548,
    SRLRI_D	= 1549,
    SRLRI_H	= 1550,
    SRLRI_W	= 1551,
    SRLR_B	= 1552,
    SRLR_D	= 1553,
    SRLR_H	= 1554,
    SRLR_W	= 1555,
    SRLV	= 1556,
    SRLV_MM	= 1557,
    SRL_B	= 1558,
    SRL_D	= 1559,
    SRL_H	= 1560,
    SRL_MM	= 1561,
    SRL_W	= 1562,
    SSNOP	= 1563,
    SSNOP_MM	= 1564,
    STORE_ACC128	= 1565,
    STORE_ACC64	= 1566,
    STORE_ACC64DSP	= 1567,
    STORE_CCOND_DSP	= 1568,
    ST_B	= 1569,
    ST_D	= 1570,
    ST_H	= 1571,
    ST_W	= 1572,
    SUB	= 1573,
    SUBQH_PH	= 1574,
    SUBQH_R_PH	= 1575,
    SUBQH_R_W	= 1576,
    SUBQH_W	= 1577,
    SUBQ_PH	= 1578,
    SUBQ_S_PH	= 1579,
    SUBQ_S_W	= 1580,
    SUBSUS_U_B	= 1581,
    SUBSUS_U_D	= 1582,
    SUBSUS_U_H	= 1583,
    SUBSUS_U_W	= 1584,
    SUBSUU_S_B	= 1585,
    SUBSUU_S_D	= 1586,
    SUBSUU_S_H	= 1587,
    SUBSUU_S_W	= 1588,
    SUBS_S_B	= 1589,
    SUBS_S_D	= 1590,
    SUBS_S_H	= 1591,
    SUBS_S_W	= 1592,
    SUBS_U_B	= 1593,
    SUBS_U_D	= 1594,
    SUBS_U_H	= 1595,
    SUBS_U_W	= 1596,
    SUBU16_MM	= 1597,
    SUBUH_QB	= 1598,
    SUBUH_R_QB	= 1599,
    SUBU_PH	= 1600,
    SUBU_QB	= 1601,
    SUBU_S_PH	= 1602,
    SUBU_S_QB	= 1603,
    SUBVI_B	= 1604,
    SUBVI_D	= 1605,
    SUBVI_H	= 1606,
    SUBVI_W	= 1607,
    SUBV_B	= 1608,
    SUBV_D	= 1609,
    SUBV_H	= 1610,
    SUBV_W	= 1611,
    SUB_MM	= 1612,
    SUBu	= 1613,
    SUBu_MM	= 1614,
    SUXC1	= 1615,
    SUXC164	= 1616,
    SUXC1_MM	= 1617,
    SW	= 1618,
    SW16_MM	= 1619,
    SW64	= 1620,
    SWC1	= 1621,
    SWC1_MM	= 1622,
    SWC2	= 1623,
    SWC2_R6	= 1624,
    SWC3	= 1625,
    SWL	= 1626,
    SWL64	= 1627,
    SWL_MM	= 1628,
    SWM16_MM	= 1629,
    SWM32_MM	= 1630,
    SWP_MM	= 1631,
    SWR	= 1632,
    SWR64	= 1633,
    SWR_MM	= 1634,
    SWSP_MM	= 1635,
    SWXC1	= 1636,
    SWXC1_MM	= 1637,
    SW_MM	= 1638,
    SYNC	= 1639,
    SYNCI	= 1640,
    SYNC_MM	= 1641,
    SYSCALL	= 1642,
    SYSCALL_MM	= 1643,
    SZ_B_PSEUDO	= 1644,
    SZ_D_PSEUDO	= 1645,
    SZ_H_PSEUDO	= 1646,
    SZ_V_PSEUDO	= 1647,
    SZ_W_PSEUDO	= 1648,
    Save16	= 1649,
    SaveX16	= 1650,
    SbRxRyOffMemX16	= 1651,
    SebRx16	= 1652,
    SehRx16	= 1653,
    SelBeqZ	= 1654,
    SelBneZ	= 1655,
    SelTBteqZCmp	= 1656,
    SelTBteqZCmpi	= 1657,
    SelTBteqZSlt	= 1658,
    SelTBteqZSlti	= 1659,
    SelTBteqZSltiu	= 1660,
    SelTBteqZSltu	= 1661,
    SelTBtneZCmp	= 1662,
    SelTBtneZCmpi	= 1663,
    SelTBtneZSlt	= 1664,
    SelTBtneZSlti	= 1665,
    SelTBtneZSltiu	= 1666,
    SelTBtneZSltu	= 1667,
    ShRxRyOffMemX16	= 1668,
    SllX16	= 1669,
    SllvRxRy16	= 1670,
    SltCCRxRy16	= 1671,
    SltRxRy16	= 1672,
    SltiCCRxImmX16	= 1673,
    SltiRxImm16	= 1674,
    SltiRxImmX16	= 1675,
    SltiuCCRxImmX16	= 1676,
    SltiuRxImm16	= 1677,
    SltiuRxImmX16	= 1678,
    SltuCCRxRy16	= 1679,
    SltuRxRy16	= 1680,
    SltuRxRyRz16	= 1681,
    SraX16	= 1682,
    SravRxRy16	= 1683,
    SrlX16	= 1684,
    SrlvRxRy16	= 1685,
    SubuRxRyRz16	= 1686,
    SwRxRyOffMemX16	= 1687,
    SwRxSpImmX16	= 1688,
    TAILCALL	= 1689,
    TAILCALL64_R	= 1690,
    TAILCALL_R	= 1691,
    TEQ	= 1692,
    TEQI	= 1693,
    TEQI_MM	= 1694,
    TEQ_MM	= 1695,
    TGE	= 1696,
    TGEI	= 1697,
    TGEIU	= 1698,
    TGEIU_MM	= 1699,
    TGEI_MM	= 1700,
    TGEU	= 1701,
    TGEU_MM	= 1702,
    TGE_MM	= 1703,
    TLBP	= 1704,
    TLBP_MM	= 1705,
    TLBR	= 1706,
    TLBR_MM	= 1707,
    TLBWI	= 1708,
    TLBWI_MM	= 1709,
    TLBWR	= 1710,
    TLBWR_MM	= 1711,
    TLT	= 1712,
    TLTI	= 1713,
    TLTIU_MM	= 1714,
    TLTI_MM	= 1715,
    TLTU	= 1716,
    TLTU_MM	= 1717,
    TLT_MM	= 1718,
    TNE	= 1719,
    TNEI	= 1720,
    TNEI_MM	= 1721,
    TNE_MM	= 1722,
    TRAP	= 1723,
    TRUNC_L_D64	= 1724,
    TRUNC_L_S	= 1725,
    TRUNC_W_D32	= 1726,
    TRUNC_W_D64	= 1727,
    TRUNC_W_MM	= 1728,
    TRUNC_W_S	= 1729,
    TRUNC_W_S_MM	= 1730,
    TTLTIU	= 1731,
    UDIV	= 1732,
    UDIV_MM	= 1733,
    V3MULU	= 1734,
    VMM0	= 1735,
    VMULU	= 1736,
    VSHF_B	= 1737,
    VSHF_D	= 1738,
    VSHF_H	= 1739,
    VSHF_W	= 1740,
    WAIT	= 1741,
    WAIT_MM	= 1742,
    WRDSP	= 1743,
    WSBH	= 1744,
    WSBH_MM	= 1745,
    XOR	= 1746,
    XOR16_MM	= 1747,
    XOR64	= 1748,
    XORI_B	= 1749,
    XOR_MM	= 1750,
    XOR_V	= 1751,
    XOR_V_D_PSEUDO	= 1752,
    XOR_V_H_PSEUDO	= 1753,
    XOR_V_W_PSEUDO	= 1754,
    XORi	= 1755,
    XORi64	= 1756,
    XORi_MM	= 1757,
    XorRxRxRy16	= 1758,
    INSTRUCTION_LIST_END = 1759
  };

namespace Sched {
  enum {
    NoInstrModel	= 0,
    II_ADDU	= 1,
    II_ADDIU	= 2,
    IIPseudo	= 3,
    II_AND	= 4,
    II_ANDI	= 5,
    IIAlu	= 6,
    IIBranch	= 7,
    II_BADDU	= 8,
    II_CEIL	= 9,
    II_CFC1	= 10,
    II_CLO	= 11,
    II_CLZ	= 12,
    II_CTC1	= 13,
    II_CVT	= 14,
    II_C_CC_D	= 15,
    II_C_CC_S	= 16,
    II_DADD	= 17,
    II_DADDIU	= 18,
    II_DADDU	= 19,
    II_DMFC1	= 20,
    II_DMTC1	= 21,
    II_DMUL	= 22,
    II_DMULT	= 23,
    II_DMULTU	= 24,
    II_POP	= 25,
    II_DROTR	= 26,
    II_DROTR32	= 27,
    II_DROTRV	= 28,
    II_DDIV	= 29,
    II_DSLL	= 30,
    II_DSLL32	= 31,
    II_DSLLV	= 32,
    II_DSRA	= 33,
    II_DSRA32	= 34,
    II_DSRAV	= 35,
    II_DSRL	= 36,
    II_DSRL32	= 37,
    II_DSRLV	= 38,
    II_DSUB	= 39,
    II_DSUBU	= 40,
    II_DDIVU	= 41,
    II_ABS	= 42,
    II_ADD_D	= 43,
    II_ADD_S	= 44,
    II_DIV_D	= 45,
    II_DIV_S	= 46,
    II_FLOOR	= 47,
    II_MOV_D	= 48,
    II_MOV_S	= 49,
    II_MUL_D	= 50,
    II_MUL_S	= 51,
    II_NEG	= 52,
    II_SQRT_D	= 53,
    II_SQRT_S	= 54,
    II_SUB_D	= 55,
    II_SUB_S	= 56,
    II_LB	= 57,
    II_LBU	= 58,
    II_LD	= 59,
    II_LDC1	= 60,
    II_LDL	= 61,
    II_LDR	= 62,
    II_LDXC1	= 63,
    II_LH	= 64,
    II_LHU	= 65,
    II_LUXC1	= 66,
    II_LUI	= 67,
    II_LW	= 68,
    II_LWC1	= 69,
    II_LWL	= 70,
    II_LWR	= 71,
    II_LWU	= 72,
    II_LWXC1	= 73,
    II_MADD	= 74,
    II_MADDU	= 75,
    II_MADD_D	= 76,
    II_MADD_S	= 77,
    II_MFC1	= 78,
    II_MFHC1	= 79,
    II_MFHI_MFLO	= 80,
    II_MOVF_D	= 81,
    II_MOVF	= 82,
    II_MOVF_S	= 83,
    II_MOVN_D	= 84,
    II_MOVN	= 85,
    II_MOVN_S	= 86,
    II_MOVT_D	= 87,
    II_MOVT	= 88,
    II_MOVT_S	= 89,
    II_MOVZ_D	= 90,
    II_MOVZ	= 91,
    II_MOVZ_S	= 92,
    II_MSUB	= 93,
    II_MSUBU	= 94,
    II_MSUB_D	= 95,
    II_MSUB_S	= 96,
    II_MTC1	= 97,
    II_MTHC1	= 98,
    II_MTHI_MTLO	= 99,
    II_MUL	= 100,
    II_MULT	= 101,
    II_MULTU	= 102,
    II_NMADD_D	= 103,
    II_NMADD_S	= 104,
    II_NMSUB_D	= 105,
    II_NMSUB_S	= 106,
    II_NOR	= 107,
    II_OR	= 108,
    II_ORI	= 109,
    II_DIV	= 110,
    II_DIVU	= 111,
    II_RDHWR	= 112,
    II_ROTR	= 113,
    II_ROTRV	= 114,
    II_ROUND	= 115,
    II_RESTORE	= 116,
    II_SB	= 117,
    II_SD	= 118,
    II_SDC1	= 119,
    II_SDL	= 120,
    II_SDR	= 121,
    II_SDXC1	= 122,
    II_SEB	= 123,
    II_SEH	= 124,
    II_SEQ_SNE	= 125,
    II_SEQI_SNEI	= 126,
    II_SH	= 127,
    II_SLL	= 128,
    II_SLLV	= 129,
    II_SLT_SLTU	= 130,
    II_SLTI_SLTIU	= 131,
    II_SRA	= 132,
    II_SRAV	= 133,
    II_SRL	= 134,
    II_SRLV	= 135,
    II_SUBU	= 136,
    II_SUXC1	= 137,
    II_SW	= 138,
    II_SWC1	= 139,
    II_SWL	= 140,
    II_SWR	= 141,
    II_SWXC1	= 142,
    II_SAVE	= 143,
    II_TRUNC	= 144,
    II_XOR	= 145,
    II_XORI	= 146,
    SCHED_LIST_END = 147
  };
} // End Sched namespace
} // End Mips namespace
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

static const uint16_t ImplicitList1[] = { Mips::DSPOutFlag20, 0 };
static const uint16_t ImplicitList2[] = { Mips::DSPCarry, 0 };
static const uint16_t ImplicitList3[] = { Mips::SP, 0 };
static const uint16_t ImplicitList4[] = { Mips::AT, 0 };
static const uint16_t ImplicitList5[] = { Mips::RA, 0 };
static const uint16_t ImplicitList6[] = { Mips::DSPPos, 0 };
static const uint16_t ImplicitList7[] = { Mips::T8, 0 };
static const uint16_t ImplicitList8[] = { Mips::DSPCCond, 0 };
static const uint16_t ImplicitList9[] = { Mips::HI0, Mips::LO0, Mips::P0, Mips::P1, Mips::P2, 0 };
static const uint16_t ImplicitList10[] = { Mips::HI0_64, Mips::LO0_64, 0 };
static const uint16_t ImplicitList11[] = { Mips::DSPOutFlag16_19, 0 };
static const uint16_t ImplicitList12[] = { Mips::HI0, Mips::LO0, 0 };
static const uint16_t ImplicitList13[] = { Mips::DSPEFI, 0 };
static const uint16_t ImplicitList14[] = { Mips::DSPPos, Mips::DSPEFI, 0 };
static const uint16_t ImplicitList15[] = { Mips::DSPOutFlag23, 0 };
static const uint16_t ImplicitList16[] = { Mips::FCC0, 0 };
static const uint16_t ImplicitList17[] = { Mips::DSPPos, Mips::DSPSCount, 0 };
static const uint16_t ImplicitList18[] = { Mips::AC0, 0 };
static const uint16_t ImplicitList19[] = { Mips::AC0_64, 0 };
static const uint16_t ImplicitList20[] = { Mips::V0, Mips::V1, 0 };
static const uint16_t ImplicitList21[] = { Mips::HI0, 0 };
static const uint16_t ImplicitList22[] = { Mips::HI0_64, 0 };
static const uint16_t ImplicitList23[] = { Mips::LO0, 0 };
static const uint16_t ImplicitList24[] = { Mips::LO0_64, 0 };
static const uint16_t ImplicitList25[] = { Mips::MPL0, Mips::P0, Mips::P1, Mips::P2, 0 };
static const uint16_t ImplicitList26[] = { Mips::MPL1, Mips::P0, Mips::P1, Mips::P2, 0 };
static const uint16_t ImplicitList27[] = { Mips::MPL2, Mips::P0, Mips::P1, Mips::P2, 0 };
static const uint16_t ImplicitList28[] = { Mips::P0, 0 };
static const uint16_t ImplicitList29[] = { Mips::P1, 0 };
static const uint16_t ImplicitList30[] = { Mips::P2, 0 };
static const uint16_t ImplicitList31[] = { Mips::DSPOutFlag21, 0 };
static const uint16_t ImplicitList32[] = { Mips::DSPOutFlag22, 0 };
static const uint16_t ImplicitList33[] = { Mips::P0, Mips::P1, Mips::P2, 0 };
static const uint16_t ImplicitList34[] = { Mips::MPL1, Mips::MPL2, Mips::P0, Mips::P1, Mips::P2, 0 };

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
static const MCOperandInfo OperandInfo12[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo13[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo14[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo15[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo16[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo17[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo18[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo19[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo20[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo21[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo22[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo23[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo24[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo25[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo26[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo27[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo28[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo29[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo30[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo31[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo32[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo33[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo34[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo35[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo36[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo37[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo38[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo39[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo40[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo41[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsPlusSPRegClassID, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo42[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo43[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo44[] = { { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo45[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo46[] = { { Mips::FCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo47[] = { { Mips::COP2RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo48[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo49[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo50[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo51[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo52[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo53[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo54[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo55[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo56[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo57[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo58[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo59[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo60[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo61[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo62[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo63[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo64[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo65[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo66[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo67[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo68[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo69[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo70[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo71[] = { { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo72[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo73[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo74[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo75[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo76[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo77[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo78[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CCRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo79[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSACtrlRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo80[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo81[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo82[] = { { Mips::FGRCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo83[] = { { Mips::FGRCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo84[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo85[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo86[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo87[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo88[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo89[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo90[] = { { Mips::CCRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo91[] = { { Mips::MSACtrlRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo92[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo93[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo94[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo95[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo96[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo97[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo98[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo99[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo100[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo101[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo102[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo103[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo104[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo105[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo106[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo107[] = { { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo108[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo109[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo110[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo111[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo112[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo113[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo114[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo115[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo116[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo117[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo118[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo119[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo120[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo121[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo122[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo123[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo124[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo125[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo126[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo127[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo128[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo129[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo130[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo131[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo132[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo133[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo134[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo135[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo136[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo137[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo138[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo139[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo140[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo141[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo142[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo143[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo144[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo145[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo146[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo147[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo148[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo149[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo150[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo151[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo152[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo153[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo154[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo155[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo156[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo157[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo158[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo159[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo160[] = { { Mips::COP2RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo161[] = { { Mips::COP3RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo162[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo163[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo164[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo165[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo166[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo167[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo168[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo169[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo170[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo171[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo172[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo173[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo174[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo175[] = { { Mips::ACC128RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo176[] = { { Mips::ACC64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo177[] = { { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo178[] = { { Mips::DSPCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo179[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo180[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo181[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, { -1, 0, MCOI::OPERAND_PCREL, 0 }, };
static const MCOperandInfo OperandInfo182[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo183[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo184[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo185[] = { { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo186[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo187[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo188[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::CPU16RegsPlusSPRegClassID, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo189[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo190[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { -1, 0, MCOI::OPERAND_IMMEDIATE, 0 }, };
static const MCOperandInfo OperandInfo191[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPUSPRegRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo192[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo193[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo194[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo195[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo196[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo197[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo198[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo199[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo200[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo201[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo202[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo203[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo204[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo205[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo206[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo207[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo208[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo209[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo210[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo211[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo212[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo213[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo214[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo215[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo216[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo217[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo218[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo219[] = { { Mips::HI32DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo220[] = { { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo221[] = { { Mips::LO32DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo222[] = { { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo223[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo224[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo225[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo226[] = { { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPRMM16RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo227[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo228[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo229[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo230[] = { { Mips::DSPCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo231[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo232[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo233[] = { { Mips::ACC128RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo234[] = { { Mips::ACC64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo235[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo236[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::ACC128RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo237[] = { { Mips::ACC64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo238[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPCCRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo239[] = { { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::AFGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo240[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo241[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo242[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo243[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo244[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::HWRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo245[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::HWRegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo246[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo247[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo248[] = { { Mips::GPRMM16ZeroRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo249[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo250[] = { { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo251[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo252[] = { { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGRCCRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo253[] = { { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGRCCRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::FGR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo254[] = { { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, { Mips::ACC64DSPRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo255[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo256[] = { { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::DSPRRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo257[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo258[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo259[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo260[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo261[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo262[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR64RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo263[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo264[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo265[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo266[] = { { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo267[] = { { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128BRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo268[] = { { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128DRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo269[] = { { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128HRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo270[] = { { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::MSA128WRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::GPR32RegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo271[] = { { 0, 0|(1<<MCOI::LookupPtrRegClass), MCOI::OPERAND_MEMORY, 0 }, { -1, 0, MCOI::OPERAND_MEMORY, 0 }, };
static const MCOperandInfo OperandInfo272[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, };
static const MCOperandInfo OperandInfo273[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo274[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, };
static const MCOperandInfo OperandInfo275[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, ((0 << 16) | (1 << MCOI::TIED_TO)) }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };
static const MCOperandInfo OperandInfo276[] = { { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { Mips::CPU16RegsRegClassID, 0, MCOI::OPERAND_REGISTER, 0 }, { -1, 0, MCOI::OPERAND_UNKNOWN, 0 }, };

extern const MCInstrDesc MipsInsts[] = {
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
  { 22,	2,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo12,0,nullptr },  // Inst #22 = ABSQ_S_PH
  { 23,	2,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo12,0,nullptr },  // Inst #23 = ABSQ_S_QB
  { 24,	2,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo13,0,nullptr },  // Inst #24 = ABSQ_S_W
  { 25,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #25 = ADD
  { 26,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #26 = ADDIUPC
  { 27,	2,	1,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #27 = ADDIUR1SP_MM
  { 28,	3,	1,	0,	2,	0|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #28 = ADDIUR2_MM
  { 29,	3,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo18,0,nullptr },  // Inst #29 = ADDIUS5_MM
  { 30,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #30 = ADDIUSP_MM
  { 31,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #31 = ADDQH_PH
  { 32,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #32 = ADDQH_R_PH
  { 33,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #33 = ADDQH_R_W
  { 34,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #34 = ADDQH_W
  { 35,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #35 = ADDQ_PH
  { 36,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #36 = ADDQ_S_PH
  { 37,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo14,0,nullptr },  // Inst #37 = ADDQ_S_W
  { 38,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList2, OperandInfo14,0,nullptr },  // Inst #38 = ADDSC
  { 39,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #39 = ADDS_A_B
  { 40,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #40 = ADDS_A_D
  { 41,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #41 = ADDS_A_H
  { 42,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #42 = ADDS_A_W
  { 43,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #43 = ADDS_S_B
  { 44,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #44 = ADDS_S_D
  { 45,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #45 = ADDS_S_H
  { 46,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #46 = ADDS_S_W
  { 47,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #47 = ADDS_U_B
  { 48,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #48 = ADDS_U_D
  { 49,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #49 = ADDS_U_H
  { 50,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #50 = ADDS_U_W
  { 51,	3,	1,	1,	2,	0|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo24,0,nullptr },  // Inst #51 = ADDU16_MM
  { 52,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #52 = ADDUH_QB
  { 53,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #53 = ADDUH_R_QB
  { 54,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #54 = ADDU_PH
  { 55,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #55 = ADDU_QB
  { 56,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #56 = ADDU_S_PH
  { 57,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #57 = ADDU_S_QB
  { 58,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #58 = ADDVI_B
  { 59,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #59 = ADDVI_D
  { 60,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #60 = ADDVI_H
  { 61,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #61 = ADDVI_W
  { 62,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #62 = ADDV_B
  { 63,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #63 = ADDV_D
  { 64,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #64 = ADDV_H
  { 65,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #65 = ADDV_W
  { 66,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, ImplicitList2, ImplicitList1, OperandInfo14,0,nullptr },  // Inst #66 = ADDWC
  { 67,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #67 = ADD_A_B
  { 68,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #68 = ADD_A_D
  { 69,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #69 = ADD_A_H
  { 70,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #70 = ADD_A_W
  { 71,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #71 = ADD_MM
  { 72,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #72 = ADDi
  { 73,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #73 = ADDi_MM
  { 74,	3,	1,	2,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #74 = ADDiu
  { 75,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #75 = ADDiu_MM
  { 76,	3,	1,	1,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #76 = ADDu
  { 77,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #77 = ADDu_MM
  { 78,	1,	0,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, OperandInfo2,0,nullptr },  // Inst #78 = ADJCALLSTACKDOWN
  { 79,	2,	0,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, OperandInfo8,0,nullptr },  // Inst #79 = ADJCALLSTACKUP
  { 80,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo30,0,nullptr },  // Inst #80 = ALIGN
  { 81,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #81 = ALUIPC
  { 82,	3,	1,	4,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #82 = AND
  { 83,	3,	1,	4,	2,	0|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo31,0,nullptr },  // Inst #83 = AND16_MM
  { 84,	3,	1,	4,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #84 = AND64
  { 85,	3,	1,	4,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #85 = ANDI16_MM
  { 86,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #86 = ANDI_B
  { 87,	3,	1,	4,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #87 = AND_MM
  { 88,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #88 = AND_V
  { 89,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #89 = AND_V_D_PSEUDO
  { 90,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #90 = AND_V_H_PSEUDO
  { 91,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #91 = AND_V_W_PSEUDO
  { 92,	3,	1,	5,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #92 = ANDi
  { 93,	3,	1,	4,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #93 = ANDi64
  { 94,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #94 = ANDi_MM
  { 95,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo34,0,nullptr },  // Inst #95 = APPEND
  { 96,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #96 = ASUB_S_B
  { 97,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #97 = ASUB_S_D
  { 98,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #98 = ASUB_S_H
  { 99,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #99 = ASUB_S_W
  { 100,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #100 = ASUB_U_B
  { 101,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #101 = ASUB_U_D
  { 102,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #102 = ASUB_U_H
  { 103,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #103 = ASUB_U_W
  { 104,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo35,0,nullptr },  // Inst #104 = ATOMIC_CMP_SWAP_I16
  { 105,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo35,0,nullptr },  // Inst #105 = ATOMIC_CMP_SWAP_I32
  { 106,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo36,0,nullptr },  // Inst #106 = ATOMIC_CMP_SWAP_I64
  { 107,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo35,0,nullptr },  // Inst #107 = ATOMIC_CMP_SWAP_I8
  { 108,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #108 = ATOMIC_LOAD_ADD_I16
  { 109,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #109 = ATOMIC_LOAD_ADD_I32
  { 110,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #110 = ATOMIC_LOAD_ADD_I64
  { 111,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #111 = ATOMIC_LOAD_ADD_I8
  { 112,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #112 = ATOMIC_LOAD_AND_I16
  { 113,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #113 = ATOMIC_LOAD_AND_I32
  { 114,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #114 = ATOMIC_LOAD_AND_I64
  { 115,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #115 = ATOMIC_LOAD_AND_I8
  { 116,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #116 = ATOMIC_LOAD_NAND_I16
  { 117,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #117 = ATOMIC_LOAD_NAND_I32
  { 118,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #118 = ATOMIC_LOAD_NAND_I64
  { 119,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #119 = ATOMIC_LOAD_NAND_I8
  { 120,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #120 = ATOMIC_LOAD_OR_I16
  { 121,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #121 = ATOMIC_LOAD_OR_I32
  { 122,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #122 = ATOMIC_LOAD_OR_I64
  { 123,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #123 = ATOMIC_LOAD_OR_I8
  { 124,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #124 = ATOMIC_LOAD_SUB_I16
  { 125,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #125 = ATOMIC_LOAD_SUB_I32
  { 126,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #126 = ATOMIC_LOAD_SUB_I64
  { 127,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #127 = ATOMIC_LOAD_SUB_I8
  { 128,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #128 = ATOMIC_LOAD_XOR_I16
  { 129,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #129 = ATOMIC_LOAD_XOR_I32
  { 130,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #130 = ATOMIC_LOAD_XOR_I64
  { 131,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #131 = ATOMIC_LOAD_XOR_I8
  { 132,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #132 = ATOMIC_SWAP_I16
  { 133,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #133 = ATOMIC_SWAP_I32
  { 134,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo38,0,nullptr },  // Inst #134 = ATOMIC_SWAP_I64
  { 135,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo37,0,nullptr },  // Inst #135 = ATOMIC_SWAP_I8
  { 136,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #136 = AUI
  { 137,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #137 = AUIPC
  { 138,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #138 = AVER_S_B
  { 139,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #139 = AVER_S_D
  { 140,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #140 = AVER_S_H
  { 141,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #141 = AVER_S_W
  { 142,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #142 = AVER_U_B
  { 143,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #143 = AVER_U_D
  { 144,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #144 = AVER_U_H
  { 145,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #145 = AVER_U_W
  { 146,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #146 = AVE_S_B
  { 147,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #147 = AVE_S_D
  { 148,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #148 = AVE_S_H
  { 149,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #149 = AVE_S_W
  { 150,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #150 = AVE_U_B
  { 151,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #151 = AVE_U_D
  { 152,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #152 = AVE_U_H
  { 153,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #153 = AVE_U_W
  { 154,	2,	1,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo39,0,nullptr },  // Inst #154 = AddiuRxImmX16
  { 155,	2,	1,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo39,0,nullptr },  // Inst #155 = AddiuRxPcImmX16
  { 156,	3,	1,	6,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo40,0,nullptr },  // Inst #156 = AddiuRxRxImm16
  { 157,	3,	1,	6,	4,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo40,0,nullptr },  // Inst #157 = AddiuRxRxImmX16
  { 158,	3,	1,	6,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo41,0,nullptr },  // Inst #158 = AddiuRxRyOffMemX16
  { 159,	1,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #159 = AddiuSpImm16
  { 160,	1,	0,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, OperandInfo5,0,nullptr },  // Inst #160 = AddiuSpImmX16
  { 161,	3,	1,	6,	2,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo42,0,nullptr },  // Inst #161 = AdduRxRyRz16
  { 162,	3,	1,	6,	2,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo43,0,nullptr },  // Inst #162 = AndRxRxRy16
  { 163,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x0ULL, nullptr, ImplicitList4, OperandInfo44,0,nullptr },  // Inst #163 = B
  { 164,	3,	1,	8,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #164 = BADDu
  { 165,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo44,0,nullptr },  // Inst #165 = BAL
  { 166,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Call)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo44,0,nullptr },  // Inst #166 = BALC
  { 167,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo34,0,nullptr },  // Inst #167 = BALIGN
  { 168,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList5, OperandInfo44,0,nullptr },  // Inst #168 = BAL_BR
  { 169,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo44,0,nullptr },  // Inst #169 = BC
  { 170,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo45,0,nullptr },  // Inst #170 = BC1EQZ
  { 171,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x5ULL, nullptr, ImplicitList4, OperandInfo46,0,nullptr },  // Inst #171 = BC1F
  { 172,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x5ULL, nullptr, ImplicitList4, OperandInfo46,0,nullptr },  // Inst #172 = BC1FL
  { 173,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, ImplicitList4, OperandInfo46,0,nullptr },  // Inst #173 = BC1F_MM
  { 174,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo45,0,nullptr },  // Inst #174 = BC1NEZ
  { 175,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x5ULL, nullptr, ImplicitList4, OperandInfo46,0,nullptr },  // Inst #175 = BC1T
  { 176,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x5ULL, nullptr, ImplicitList4, OperandInfo46,0,nullptr },  // Inst #176 = BC1TL
  { 177,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, ImplicitList4, OperandInfo46,0,nullptr },  // Inst #177 = BC1T_MM
  { 178,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo47,0,nullptr },  // Inst #178 = BC2EQZ
  { 179,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo47,0,nullptr },  // Inst #179 = BC2NEZ
  { 180,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #180 = BCLRI_B
  { 181,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #181 = BCLRI_D
  { 182,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #182 = BCLRI_H
  { 183,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #183 = BCLRI_W
  { 184,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #184 = BCLR_B
  { 185,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #185 = BCLR_D
  { 186,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #186 = BCLR_H
  { 187,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #187 = BCLR_W
  { 188,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #188 = BEQ
  { 189,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo49,0,nullptr },  // Inst #189 = BEQ64
  { 190,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #190 = BEQC
  { 191,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #191 = BEQL
  { 192,	2,	0,	7,	2,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList4, OperandInfo50,0,nullptr },  // Inst #192 = BEQZ16_MM
  { 193,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #193 = BEQZALC
  { 194,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #194 = BEQZC
  { 195,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #195 = BEQZC_MM
  { 196,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #196 = BEQ_MM
  { 197,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #197 = BGEC
  { 198,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #198 = BGEUC
  { 199,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #199 = BGEZ
  { 200,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo52,0,nullptr },  // Inst #200 = BGEZ64
  { 201,	2,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #201 = BGEZAL
  { 202,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #202 = BGEZALC
  { 203,	2,	0,	7,	4,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #203 = BGEZALL
  { 204,	2,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #204 = BGEZALS_MM
  { 205,	2,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #205 = BGEZAL_MM
  { 206,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #206 = BGEZC
  { 207,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #207 = BGEZL
  { 208,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #208 = BGEZ_MM
  { 209,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #209 = BGTZ
  { 210,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo52,0,nullptr },  // Inst #210 = BGTZ64
  { 211,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #211 = BGTZALC
  { 212,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #212 = BGTZC
  { 213,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #213 = BGTZL
  { 214,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #214 = BGTZ_MM
  { 215,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo53,0,nullptr },  // Inst #215 = BINSLI_B
  { 216,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo54,0,nullptr },  // Inst #216 = BINSLI_D
  { 217,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo55,0,nullptr },  // Inst #217 = BINSLI_H
  { 218,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo56,0,nullptr },  // Inst #218 = BINSLI_W
  { 219,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #219 = BINSL_B
  { 220,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #220 = BINSL_D
  { 221,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #221 = BINSL_H
  { 222,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #222 = BINSL_W
  { 223,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo53,0,nullptr },  // Inst #223 = BINSRI_B
  { 224,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo54,0,nullptr },  // Inst #224 = BINSRI_D
  { 225,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo55,0,nullptr },  // Inst #225 = BINSRI_H
  { 226,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo56,0,nullptr },  // Inst #226 = BINSRI_W
  { 227,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #227 = BINSR_B
  { 228,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #228 = BINSR_D
  { 229,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #229 = BINSR_H
  { 230,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #230 = BINSR_W
  { 231,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #231 = BITREV
  { 232,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #232 = BITSWAP
  { 233,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #233 = BLEZ
  { 234,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo52,0,nullptr },  // Inst #234 = BLEZ64
  { 235,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #235 = BLEZALC
  { 236,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #236 = BLEZC
  { 237,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #237 = BLEZL
  { 238,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #238 = BLEZ_MM
  { 239,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #239 = BLTC
  { 240,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #240 = BLTUC
  { 241,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #241 = BLTZ
  { 242,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo52,0,nullptr },  // Inst #242 = BLTZ64
  { 243,	2,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #243 = BLTZAL
  { 244,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #244 = BLTZALC
  { 245,	2,	0,	7,	4,	0|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #245 = BLTZALL
  { 246,	2,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #246 = BLTZALS_MM
  { 247,	2,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #247 = BLTZAL_MM
  { 248,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #248 = BLTZC
  { 249,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #249 = BLTZL
  { 250,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #250 = BLTZ_MM
  { 251,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo53,0,nullptr },  // Inst #251 = BMNZI_B
  { 252,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #252 = BMNZ_V
  { 253,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo53,0,nullptr },  // Inst #253 = BMZI_B
  { 254,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #254 = BMZ_V
  { 255,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #255 = BNE
  { 256,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo49,0,nullptr },  // Inst #256 = BNE64
  { 257,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #257 = BNEC
  { 258,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #258 = BNEGI_B
  { 259,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #259 = BNEGI_D
  { 260,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #260 = BNEGI_H
  { 261,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #261 = BNEGI_W
  { 262,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #262 = BNEG_B
  { 263,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #263 = BNEG_D
  { 264,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #264 = BNEG_H
  { 265,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #265 = BNEG_W
  { 266,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x2ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #266 = BNEL
  { 267,	2,	0,	7,	2,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList4, OperandInfo50,0,nullptr },  // Inst #267 = BNEZ16_MM
  { 268,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo51,0,nullptr },  // Inst #268 = BNEZALC
  { 269,	2,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #269 = BNEZC
  { 270,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo51,0,nullptr },  // Inst #270 = BNEZC_MM
  { 271,	3,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #271 = BNE_MM
  { 272,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #272 = BNVC
  { 273,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo61,0,nullptr },  // Inst #273 = BNZ_B
  { 274,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo62,0,nullptr },  // Inst #274 = BNZ_D
  { 275,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo63,0,nullptr },  // Inst #275 = BNZ_H
  { 276,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo61,0,nullptr },  // Inst #276 = BNZ_V
  { 277,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo64,0,nullptr },  // Inst #277 = BNZ_W
  { 278,	3,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo48,0,nullptr },  // Inst #278 = BOVC
  { 279,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo44,0,nullptr },  // Inst #279 = BPOSGE32
  { 280,	1,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayLoad)|(1<<MCID::UsesCustomInserter), 0x0ULL, ImplicitList6, nullptr, OperandInfo65,0,nullptr },  // Inst #280 = BPOSGE32_PSEUDO
  { 281,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo7,0,nullptr },  // Inst #281 = BREAK
  { 282,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #282 = BREAK16_MM
  { 283,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo7,0,nullptr },  // Inst #283 = BREAK_MM
  { 284,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo53,0,nullptr },  // Inst #284 = BSELI_B
  { 285,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #285 = BSEL_D_PSEUDO
  { 286,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #286 = BSEL_FD_PSEUDO
  { 287,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #287 = BSEL_FW_PSEUDO
  { 288,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #288 = BSEL_H_PSEUDO
  { 289,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #289 = BSEL_V
  { 290,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #290 = BSEL_W_PSEUDO
  { 291,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #291 = BSETI_B
  { 292,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #292 = BSETI_D
  { 293,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #293 = BSETI_H
  { 294,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #294 = BSETI_W
  { 295,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #295 = BSET_B
  { 296,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #296 = BSET_D
  { 297,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #297 = BSET_H
  { 298,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #298 = BSET_W
  { 299,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo61,0,nullptr },  // Inst #299 = BZ_B
  { 300,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo62,0,nullptr },  // Inst #300 = BZ_D
  { 301,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo63,0,nullptr },  // Inst #301 = BZ_H
  { 302,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo61,0,nullptr },  // Inst #302 = BZ_V
  { 303,	2,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo64,0,nullptr },  // Inst #303 = BZ_W
  { 304,	2,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo66,0,nullptr },  // Inst #304 = BeqzRxImm16
  { 305,	2,	0,	6,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo66,0,nullptr },  // Inst #305 = BeqzRxImmX16
  { 306,	1,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo44,0,nullptr },  // Inst #306 = Bimm16
  { 307,	1,	0,	6,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo44,0,nullptr },  // Inst #307 = BimmX16
  { 308,	2,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo66,0,nullptr },  // Inst #308 = BnezRxImm16
  { 309,	2,	0,	6,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo66,0,nullptr },  // Inst #309 = BnezRxImmX16
  { 310,	0,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #310 = Break16
  { 311,	1,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList7, nullptr, OperandInfo5,0,nullptr },  // Inst #311 = Bteqz16
  { 312,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo67,0,nullptr },  // Inst #312 = BteqzT8CmpX16
  { 313,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo68,0,nullptr },  // Inst #313 = BteqzT8CmpiX16
  { 314,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo67,0,nullptr },  // Inst #314 = BteqzT8SltX16
  { 315,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo68,0,nullptr },  // Inst #315 = BteqzT8SltiX16
  { 316,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo68,0,nullptr },  // Inst #316 = BteqzT8SltiuX16
  { 317,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo67,0,nullptr },  // Inst #317 = BteqzT8SltuX16
  { 318,	1,	0,	6,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList7, nullptr, OperandInfo5,0,nullptr },  // Inst #318 = BteqzX16
  { 319,	1,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList7, nullptr, OperandInfo5,0,nullptr },  // Inst #319 = Btnez16
  { 320,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo67,0,nullptr },  // Inst #320 = BtnezT8CmpX16
  { 321,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo68,0,nullptr },  // Inst #321 = BtnezT8CmpiX16
  { 322,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo67,0,nullptr },  // Inst #322 = BtnezT8SltX16
  { 323,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo68,0,nullptr },  // Inst #323 = BtnezT8SltiX16
  { 324,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo68,0,nullptr },  // Inst #324 = BtnezT8SltiuX16
  { 325,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo67,0,nullptr },  // Inst #325 = BtnezT8SltuX16
  { 326,	1,	0,	6,	4,	0|(1<<MCID::Branch)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList7, nullptr, OperandInfo5,0,nullptr },  // Inst #326 = BtnezX16
  { 327,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo69,0,nullptr },  // Inst #327 = BuildPairF64
  { 328,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo70,0,nullptr },  // Inst #328 = BuildPairF64_64
  { 329,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo71,0,nullptr },  // Inst #329 = CACHE
  { 330,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo72,0,nullptr },  // Inst #330 = CACHE_MM
  { 331,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo71,0,nullptr },  // Inst #331 = CACHE_R6
  { 332,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #332 = CEIL_L_D64
  { 333,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #333 = CEIL_L_S
  { 334,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #334 = CEIL_W_D32
  { 335,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #335 = CEIL_W_D64
  { 336,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #336 = CEIL_W_MM
  { 337,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #337 = CEIL_W_S
  { 338,	2,	1,	9,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #338 = CEIL_W_S_MM
  { 339,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #339 = CEQI_B
  { 340,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #340 = CEQI_D
  { 341,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #341 = CEQI_H
  { 342,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #342 = CEQI_W
  { 343,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #343 = CEQ_B
  { 344,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #344 = CEQ_D
  { 345,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #345 = CEQ_H
  { 346,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #346 = CEQ_W
  { 347,	2,	1,	10,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo78,0,nullptr },  // Inst #347 = CFC1
  { 348,	2,	1,	10,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo78,0,nullptr },  // Inst #348 = CFC1_MM
  { 349,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo79,0,nullptr },  // Inst #349 = CFCMSA
  { 350,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #350 = CINS
  { 351,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #351 = CINS32
  { 352,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #352 = CLASS_D
  { 353,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #353 = CLASS_S
  { 354,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #354 = CLEI_S_B
  { 355,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #355 = CLEI_S_D
  { 356,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #356 = CLEI_S_H
  { 357,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #357 = CLEI_S_W
  { 358,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #358 = CLEI_U_B
  { 359,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #359 = CLEI_U_D
  { 360,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #360 = CLEI_U_H
  { 361,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #361 = CLEI_U_W
  { 362,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #362 = CLE_S_B
  { 363,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #363 = CLE_S_D
  { 364,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #364 = CLE_S_H
  { 365,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #365 = CLE_S_W
  { 366,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #366 = CLE_U_B
  { 367,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #367 = CLE_U_D
  { 368,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #368 = CLE_U_H
  { 369,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #369 = CLE_U_W
  { 370,	2,	1,	11,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #370 = CLO
  { 371,	2,	1,	11,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #371 = CLO_MM
  { 372,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #372 = CLO_R6
  { 373,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #373 = CLTI_S_B
  { 374,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #374 = CLTI_S_D
  { 375,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #375 = CLTI_S_H
  { 376,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #376 = CLTI_S_W
  { 377,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #377 = CLTI_U_B
  { 378,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #378 = CLTI_U_D
  { 379,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #379 = CLTI_U_H
  { 380,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #380 = CLTI_U_W
  { 381,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #381 = CLT_S_B
  { 382,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #382 = CLT_S_D
  { 383,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #383 = CLT_S_H
  { 384,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #384 = CLT_S_W
  { 385,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #385 = CLT_U_B
  { 386,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #386 = CLT_U_D
  { 387,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #387 = CLT_U_H
  { 388,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #388 = CLT_U_W
  { 389,	2,	1,	12,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #389 = CLZ
  { 390,	2,	1,	12,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #390 = CLZ_MM
  { 391,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #391 = CLZ_R6
  { 392,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo81,0,nullptr },  // Inst #392 = CMPGDU_EQ_QB
  { 393,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo81,0,nullptr },  // Inst #393 = CMPGDU_LE_QB
  { 394,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo81,0,nullptr },  // Inst #394 = CMPGDU_LT_QB
  { 395,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo81,0,nullptr },  // Inst #395 = CMPGU_EQ_QB
  { 396,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo81,0,nullptr },  // Inst #396 = CMPGU_LE_QB
  { 397,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo81,0,nullptr },  // Inst #397 = CMPGU_LT_QB
  { 398,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo12,0,nullptr },  // Inst #398 = CMPU_EQ_QB
  { 399,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo12,0,nullptr },  // Inst #399 = CMPU_LE_QB
  { 400,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo12,0,nullptr },  // Inst #400 = CMPU_LT_QB
  { 401,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #401 = CMP_EQ_D
  { 402,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo12,0,nullptr },  // Inst #402 = CMP_EQ_PH
  { 403,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #403 = CMP_EQ_S
  { 404,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #404 = CMP_F_D
  { 405,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #405 = CMP_F_S
  { 406,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #406 = CMP_LE_D
  { 407,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo12,0,nullptr },  // Inst #407 = CMP_LE_PH
  { 408,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #408 = CMP_LE_S
  { 409,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #409 = CMP_LT_D
  { 410,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList8, OperandInfo12,0,nullptr },  // Inst #410 = CMP_LT_PH
  { 411,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #411 = CMP_LT_S
  { 412,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #412 = CMP_SAF_D
  { 413,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #413 = CMP_SAF_S
  { 414,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #414 = CMP_SEQ_D
  { 415,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #415 = CMP_SEQ_S
  { 416,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #416 = CMP_SLE_D
  { 417,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #417 = CMP_SLE_S
  { 418,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #418 = CMP_SLT_D
  { 419,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #419 = CMP_SLT_S
  { 420,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #420 = CMP_SUEQ_D
  { 421,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #421 = CMP_SUEQ_S
  { 422,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #422 = CMP_SULE_D
  { 423,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #423 = CMP_SULE_S
  { 424,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #424 = CMP_SULT_D
  { 425,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #425 = CMP_SULT_S
  { 426,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #426 = CMP_SUN_D
  { 427,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #427 = CMP_SUN_S
  { 428,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #428 = CMP_UEQ_D
  { 429,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #429 = CMP_UEQ_S
  { 430,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #430 = CMP_ULE_D
  { 431,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #431 = CMP_ULE_S
  { 432,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #432 = CMP_ULT_D
  { 433,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #433 = CMP_ULT_S
  { 434,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo82,0,nullptr },  // Inst #434 = CMP_UN_D
  { 435,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo83,0,nullptr },  // Inst #435 = CMP_UN_S
  { 436,	3,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::NotDuplicable), 0x0ULL, nullptr, nullptr, OperandInfo3,0,nullptr },  // Inst #436 = CONSTPOOL_ENTRY
  { 437,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo84,0,nullptr },  // Inst #437 = COPY_FD_PSEUDO
  { 438,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo85,0,nullptr },  // Inst #438 = COPY_FW_PSEUDO
  { 439,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo86,0,nullptr },  // Inst #439 = COPY_S_B
  { 440,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo87,0,nullptr },  // Inst #440 = COPY_S_D
  { 441,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo88,0,nullptr },  // Inst #441 = COPY_S_H
  { 442,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo89,0,nullptr },  // Inst #442 = COPY_S_W
  { 443,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo86,0,nullptr },  // Inst #443 = COPY_U_B
  { 444,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo87,0,nullptr },  // Inst #444 = COPY_U_D
  { 445,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo88,0,nullptr },  // Inst #445 = COPY_U_H
  { 446,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo89,0,nullptr },  // Inst #446 = COPY_U_W
  { 447,	2,	1,	13,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo90,0,nullptr },  // Inst #447 = CTC1
  { 448,	2,	1,	13,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo90,0,nullptr },  // Inst #448 = CTC1_MM
  { 449,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo91,0,nullptr },  // Inst #449 = CTCMSA
  { 450,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo92,0,nullptr },  // Inst #450 = CVT_D32_S
  { 451,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo92,0,nullptr },  // Inst #451 = CVT_D32_W
  { 452,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo92,0,nullptr },  // Inst #452 = CVT_D32_W_MM
  { 453,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #453 = CVT_D64_L
  { 454,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #454 = CVT_D64_S
  { 455,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #455 = CVT_D64_W
  { 456,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo92,0,nullptr },  // Inst #456 = CVT_D_S_MM
  { 457,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #457 = CVT_L_D64
  { 458,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #458 = CVT_L_D64_MM
  { 459,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #459 = CVT_L_S
  { 460,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #460 = CVT_L_S_MM
  { 461,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #461 = CVT_S_D32
  { 462,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #462 = CVT_S_D32_MM
  { 463,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #463 = CVT_S_D64
  { 464,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #464 = CVT_S_L
  { 465,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #465 = CVT_S_W
  { 466,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #466 = CVT_S_W_MM
  { 467,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #467 = CVT_W_D32
  { 468,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #468 = CVT_W_D64
  { 469,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #469 = CVT_W_MM
  { 470,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #470 = CVT_W_S
  { 471,	2,	1,	14,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #471 = CVT_W_S_MM
  { 472,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #472 = C_EQ_D32
  { 473,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #473 = C_EQ_D64
  { 474,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #474 = C_EQ_S
  { 475,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #475 = C_F_D32
  { 476,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #476 = C_F_D64
  { 477,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #477 = C_F_S
  { 478,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #478 = C_LE_D32
  { 479,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #479 = C_LE_D64
  { 480,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #480 = C_LE_S
  { 481,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #481 = C_LT_D32
  { 482,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #482 = C_LT_D64
  { 483,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #483 = C_LT_S
  { 484,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #484 = C_NGE_D32
  { 485,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #485 = C_NGE_D64
  { 486,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #486 = C_NGE_S
  { 487,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #487 = C_NGLE_D32
  { 488,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #488 = C_NGLE_D64
  { 489,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #489 = C_NGLE_S
  { 490,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #490 = C_NGL_D32
  { 491,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #491 = C_NGL_D64
  { 492,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #492 = C_NGL_S
  { 493,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #493 = C_NGT_D32
  { 494,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #494 = C_NGT_D64
  { 495,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #495 = C_NGT_S
  { 496,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #496 = C_OLE_D32
  { 497,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #497 = C_OLE_D64
  { 498,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #498 = C_OLE_S
  { 499,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #499 = C_OLT_D32
  { 500,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #500 = C_OLT_D64
  { 501,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #501 = C_OLT_S
  { 502,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #502 = C_SEQ_D32
  { 503,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #503 = C_SEQ_D64
  { 504,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #504 = C_SEQ_S
  { 505,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #505 = C_SF_D32
  { 506,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #506 = C_SF_D64
  { 507,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #507 = C_SF_S
  { 508,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #508 = C_UEQ_D32
  { 509,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #509 = C_UEQ_D64
  { 510,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #510 = C_UEQ_S
  { 511,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #511 = C_ULE_D32
  { 512,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #512 = C_ULE_D64
  { 513,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #513 = C_ULE_S
  { 514,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #514 = C_ULT_D32
  { 515,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #515 = C_ULT_D64
  { 516,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #516 = C_ULT_S
  { 517,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #517 = C_UN_D32
  { 518,	2,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #518 = C_UN_D64
  { 519,	2,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #519 = C_UN_S
  { 520,	2,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo94,0,nullptr },  // Inst #520 = CmpRxRy16
  { 521,	2,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo39,0,nullptr },  // Inst #521 = CmpiRxImm16
  { 522,	2,	0,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo39,0,nullptr },  // Inst #522 = CmpiRxImmX16
  { 523,	1,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #523 = Constant32
  { 524,	3,	1,	17,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #524 = DADD
  { 525,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #525 = DADDi
  { 526,	3,	1,	18,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #526 = DADDiu
  { 527,	3,	1,	19,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #527 = DADDu
  { 528,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo95,0,nullptr },  // Inst #528 = DAHI
  { 529,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo96,0,nullptr },  // Inst #529 = DALIGN
  { 530,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo95,0,nullptr },  // Inst #530 = DATI
  { 531,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #531 = DAUI
  { 532,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #532 = DBITSWAP
  { 533,	2,	1,	11,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #533 = DCLO
  { 534,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #534 = DCLO_R6
  { 535,	2,	1,	12,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #535 = DCLZ
  { 536,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #536 = DCLZ_R6
  { 537,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #537 = DDIV
  { 538,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #538 = DDIVU
  { 539,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #539 = DERET
  { 540,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #540 = DERET_MM
  { 541,	4,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #541 = DEXT
  { 542,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #542 = DEXTM
  { 543,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #543 = DEXTU
  { 544,	1,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #544 = DI
  { 545,	5,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo98,0,nullptr },  // Inst #545 = DINS
  { 546,	5,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo98,0,nullptr },  // Inst #546 = DINSM
  { 547,	5,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo98,0,nullptr },  // Inst #547 = DINSU
  { 548,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #548 = DIV
  { 549,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #549 = DIVU
  { 550,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #550 = DIV_S_B
  { 551,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #551 = DIV_S_D
  { 552,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #552 = DIV_S_H
  { 553,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #553 = DIV_S_W
  { 554,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #554 = DIV_U_B
  { 555,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #555 = DIV_U_D
  { 556,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #556 = DIV_U_H
  { 557,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #557 = DIV_U_W
  { 558,	1,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #558 = DI_MM
  { 559,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo96,0,nullptr },  // Inst #559 = DLSA
  { 560,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo96,0,nullptr },  // Inst #560 = DLSA_R6
  { 561,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #561 = DMFC0
  { 562,	2,	1,	20,	4,	0|(1<<MCID::Bitcast), 0x4ULL, nullptr, nullptr, OperandInfo99,0,nullptr },  // Inst #562 = DMFC1
  { 563,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #563 = DMFC2
  { 564,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #564 = DMOD
  { 565,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #565 = DMODU
  { 566,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #566 = DMTC0
  { 567,	2,	1,	21,	4,	0|(1<<MCID::Bitcast), 0x4ULL, nullptr, nullptr, OperandInfo100,0,nullptr },  // Inst #567 = DMTC1
  { 568,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #568 = DMTC2
  { 569,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #569 = DMUH
  { 570,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #570 = DMUHU
  { 571,	3,	1,	22,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, ImplicitList9, OperandInfo32,0,nullptr },  // Inst #571 = DMUL
  { 572,	2,	0,	23,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, ImplicitList10, OperandInfo97,0,nullptr },  // Inst #572 = DMULT
  { 573,	2,	0,	24,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, ImplicitList10, OperandInfo97,0,nullptr },  // Inst #573 = DMULTu
  { 574,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #574 = DMULU
  { 575,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #575 = DMUL_R6
  { 576,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo101,0,nullptr },  // Inst #576 = DOTP_S_D
  { 577,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo102,0,nullptr },  // Inst #577 = DOTP_S_H
  { 578,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo103,0,nullptr },  // Inst #578 = DOTP_S_W
  { 579,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo101,0,nullptr },  // Inst #579 = DOTP_U_D
  { 580,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo102,0,nullptr },  // Inst #580 = DOTP_U_H
  { 581,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo103,0,nullptr },  // Inst #581 = DOTP_U_W
  { 582,	4,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo104,0,nullptr },  // Inst #582 = DPADD_S_D
  { 583,	4,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo105,0,nullptr },  // Inst #583 = DPADD_S_H
  { 584,	4,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo106,0,nullptr },  // Inst #584 = DPADD_S_W
  { 585,	4,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo104,0,nullptr },  // Inst #585 = DPADD_U_D
  { 586,	4,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo105,0,nullptr },  // Inst #586 = DPADD_U_H
  { 587,	4,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo106,0,nullptr },  // Inst #587 = DPADD_U_W
  { 588,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #588 = DPAQX_SA_W_PH
  { 589,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #589 = DPAQX_S_W_PH
  { 590,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #590 = DPAQ_SA_L_W
  { 591,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #591 = DPAQ_S_W_PH
  { 592,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #592 = DPAU_H_QBL
  { 593,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #593 = DPAU_H_QBR
  { 594,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #594 = DPAX_W_PH
  { 595,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #595 = DPA_W_PH
  { 596,	2,	1,	25,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #596 = DPOP
  { 597,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #597 = DPSQX_SA_W_PH
  { 598,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #598 = DPSQX_S_W_PH
  { 599,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #599 = DPSQ_SA_L_W
  { 600,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #600 = DPSQ_S_W_PH
  { 601,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo104,0,nullptr },  // Inst #601 = DPSUB_S_D
  { 602,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo105,0,nullptr },  // Inst #602 = DPSUB_S_H
  { 603,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo106,0,nullptr },  // Inst #603 = DPSUB_S_W
  { 604,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo104,0,nullptr },  // Inst #604 = DPSUB_U_D
  { 605,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo105,0,nullptr },  // Inst #605 = DPSUB_U_H
  { 606,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo106,0,nullptr },  // Inst #606 = DPSUB_U_W
  { 607,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #607 = DPSU_H_QBL
  { 608,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #608 = DPSU_H_QBR
  { 609,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #609 = DPSX_W_PH
  { 610,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #610 = DPS_W_PH
  { 611,	3,	1,	26,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #611 = DROTR
  { 612,	3,	1,	27,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #612 = DROTR32
  { 613,	3,	1,	28,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo108,0,nullptr },  // Inst #613 = DROTRV
  { 614,	2,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #614 = DSBH
  { 615,	2,	0,	29,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList10, OperandInfo97,0,nullptr },  // Inst #615 = DSDIV
  { 616,	2,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #616 = DSHD
  { 617,	3,	1,	30,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #617 = DSLL
  { 618,	3,	1,	31,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #618 = DSLL32
  { 619,	2,	1,	30,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo109,0,nullptr },  // Inst #619 = DSLL64_32
  { 620,	3,	1,	32,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo108,0,nullptr },  // Inst #620 = DSLLV
  { 621,	3,	1,	33,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #621 = DSRA
  { 622,	3,	1,	34,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #622 = DSRA32
  { 623,	3,	1,	35,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo108,0,nullptr },  // Inst #623 = DSRAV
  { 624,	3,	1,	36,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #624 = DSRL
  { 625,	3,	1,	37,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #625 = DSRL32
  { 626,	3,	1,	38,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo108,0,nullptr },  // Inst #626 = DSRLV
  { 627,	3,	1,	39,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #627 = DSUB
  { 628,	3,	1,	40,	4,	0|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #628 = DSUBu
  { 629,	2,	0,	41,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList10, OperandInfo97,0,nullptr },  // Inst #629 = DUDIV
  { 630,	2,	0,	6,	2,	0, 0x0ULL, nullptr, ImplicitList12, OperandInfo94,0,nullptr },  // Inst #630 = DivRxRy16
  { 631,	2,	0,	6,	2,	0, 0x0ULL, nullptr, ImplicitList12, OperandInfo94,0,nullptr },  // Inst #631 = DivuRxRy16
  { 632,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #632 = EHB
  { 633,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #633 = EHB_MM
  { 634,	1,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #634 = EI
  { 635,	1,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #635 = EI_MM
  { 636,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #636 = ERET
  { 637,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #637 = ERET_MM
  { 638,	4,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo110,0,nullptr },  // Inst #638 = EXT
  { 639,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, ImplicitList6, ImplicitList13, OperandInfo111,0,nullptr },  // Inst #639 = EXTP
  { 640,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, ImplicitList6, ImplicitList14, OperandInfo111,0,nullptr },  // Inst #640 = EXTPDP
  { 641,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, ImplicitList6, ImplicitList14, OperandInfo112,0,nullptr },  // Inst #641 = EXTPDPV
  { 642,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, ImplicitList6, ImplicitList13, OperandInfo112,0,nullptr },  // Inst #642 = EXTPV
  { 643,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo112,0,nullptr },  // Inst #643 = EXTRV_RS_W
  { 644,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo112,0,nullptr },  // Inst #644 = EXTRV_R_W
  { 645,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo112,0,nullptr },  // Inst #645 = EXTRV_S_H
  { 646,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo112,0,nullptr },  // Inst #646 = EXTRV_W
  { 647,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo111,0,nullptr },  // Inst #647 = EXTR_RS_W
  { 648,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo111,0,nullptr },  // Inst #648 = EXTR_R_W
  { 649,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo111,0,nullptr },  // Inst #649 = EXTR_S_H
  { 650,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList15, OperandInfo111,0,nullptr },  // Inst #650 = EXTR_W
  { 651,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #651 = EXTS
  { 652,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo80,0,nullptr },  // Inst #652 = EXTS32
  { 653,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo110,0,nullptr },  // Inst #653 = EXT_MM
  { 654,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo113,0,nullptr },  // Inst #654 = ExtractElementF64
  { 655,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo114,0,nullptr },  // Inst #655 = ExtractElementF64_64
  { 656,	2,	1,	0,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #656 = FABS_D
  { 657,	2,	1,	42,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #657 = FABS_D32
  { 658,	2,	1,	42,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #658 = FABS_D64
  { 659,	2,	1,	42,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #659 = FABS_MM
  { 660,	2,	1,	42,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #660 = FABS_S
  { 661,	2,	1,	42,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #661 = FABS_S_MM
  { 662,	2,	1,	0,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #662 = FABS_W
  { 663,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #663 = FADD_D
  { 664,	3,	1,	43,	4,	0|(1<<MCID::Commutable), 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #664 = FADD_D32
  { 665,	3,	1,	43,	4,	0|(1<<MCID::Commutable), 0x4ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #665 = FADD_D64
  { 666,	3,	1,	43,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #666 = FADD_MM
  { 667,	3,	1,	44,	4,	0|(1<<MCID::Commutable), 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #667 = FADD_S
  { 668,	3,	1,	44,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #668 = FADD_S_MM
  { 669,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #669 = FADD_W
  { 670,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #670 = FCAF_D
  { 671,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #671 = FCAF_W
  { 672,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #672 = FCEQ_D
  { 673,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #673 = FCEQ_W
  { 674,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #674 = FCLASS_D
  { 675,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #675 = FCLASS_W
  { 676,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #676 = FCLE_D
  { 677,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #677 = FCLE_W
  { 678,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #678 = FCLT_D
  { 679,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #679 = FCLT_W
  { 680,	3,	0,	15,	4,	0, 0x4ULL, nullptr, ImplicitList16, OperandInfo120,0,nullptr },  // Inst #680 = FCMP_D32
  { 681,	3,	0,	15,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, ImplicitList16, OperandInfo120,0,nullptr },  // Inst #681 = FCMP_D32_MM
  { 682,	3,	0,	15,	4,	0, 0x4ULL, nullptr, ImplicitList16, OperandInfo121,0,nullptr },  // Inst #682 = FCMP_D64
  { 683,	3,	0,	16,	4,	0, 0x4ULL, nullptr, ImplicitList16, OperandInfo122,0,nullptr },  // Inst #683 = FCMP_S32
  { 684,	3,	0,	16,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, ImplicitList16, OperandInfo122,0,nullptr },  // Inst #684 = FCMP_S32_MM
  { 685,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #685 = FCNE_D
  { 686,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #686 = FCNE_W
  { 687,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #687 = FCOR_D
  { 688,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #688 = FCOR_W
  { 689,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #689 = FCUEQ_D
  { 690,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #690 = FCUEQ_W
  { 691,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #691 = FCULE_D
  { 692,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #692 = FCULE_W
  { 693,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #693 = FCULT_D
  { 694,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #694 = FCULT_W
  { 695,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #695 = FCUNE_D
  { 696,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #696 = FCUNE_W
  { 697,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #697 = FCUN_D
  { 698,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #698 = FCUN_W
  { 699,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #699 = FDIV_D
  { 700,	3,	1,	45,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #700 = FDIV_D32
  { 701,	3,	1,	45,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #701 = FDIV_D64
  { 702,	3,	1,	45,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #702 = FDIV_MM
  { 703,	3,	1,	46,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #703 = FDIV_S
  { 704,	3,	1,	46,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #704 = FDIV_S_MM
  { 705,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #705 = FDIV_W
  { 706,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo123,0,nullptr },  // Inst #706 = FEXDO_H
  { 707,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo124,0,nullptr },  // Inst #707 = FEXDO_W
  { 708,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #708 = FEXP2_D
  { 709,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #709 = FEXP2_D_1_PSEUDO
  { 710,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #710 = FEXP2_W
  { 711,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #711 = FEXP2_W_1_PSEUDO
  { 712,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo125,0,nullptr },  // Inst #712 = FEXUPL_D
  { 713,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo126,0,nullptr },  // Inst #713 = FEXUPL_W
  { 714,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo125,0,nullptr },  // Inst #714 = FEXUPR_D
  { 715,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo126,0,nullptr },  // Inst #715 = FEXUPR_W
  { 716,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #716 = FFINT_S_D
  { 717,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #717 = FFINT_S_W
  { 718,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #718 = FFINT_U_D
  { 719,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #719 = FFINT_U_W
  { 720,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo125,0,nullptr },  // Inst #720 = FFQL_D
  { 721,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo126,0,nullptr },  // Inst #721 = FFQL_W
  { 722,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo125,0,nullptr },  // Inst #722 = FFQR_D
  { 723,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo126,0,nullptr },  // Inst #723 = FFQR_W
  { 724,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo127,0,nullptr },  // Inst #724 = FILL_B
  { 725,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo128,0,nullptr },  // Inst #725 = FILL_D
  { 726,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo129,0,nullptr },  // Inst #726 = FILL_FD_PSEUDO
  { 727,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo130,0,nullptr },  // Inst #727 = FILL_FW_PSEUDO
  { 728,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo131,0,nullptr },  // Inst #728 = FILL_H
  { 729,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo132,0,nullptr },  // Inst #729 = FILL_W
  { 730,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #730 = FLOG2_D
  { 731,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #731 = FLOG2_W
  { 732,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #732 = FLOOR_L_D64
  { 733,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #733 = FLOOR_L_S
  { 734,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #734 = FLOOR_W_D32
  { 735,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #735 = FLOOR_W_D64
  { 736,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #736 = FLOOR_W_MM
  { 737,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #737 = FLOOR_W_S
  { 738,	2,	1,	47,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #738 = FLOOR_W_S_MM
  { 739,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #739 = FMADD_D
  { 740,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #740 = FMADD_W
  { 741,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #741 = FMAX_A_D
  { 742,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #742 = FMAX_A_W
  { 743,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #743 = FMAX_D
  { 744,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #744 = FMAX_W
  { 745,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #745 = FMIN_A_D
  { 746,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #746 = FMIN_A_W
  { 747,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #747 = FMIN_D
  { 748,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #748 = FMIN_W
  { 749,	2,	1,	48,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #749 = FMOV_D32
  { 750,	2,	1,	48,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #750 = FMOV_D32_MM
  { 751,	2,	1,	48,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #751 = FMOV_D64
  { 752,	2,	1,	49,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #752 = FMOV_S
  { 753,	2,	1,	49,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #753 = FMOV_S_MM
  { 754,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #754 = FMSUB_D
  { 755,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #755 = FMSUB_W
  { 756,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #756 = FMUL_D
  { 757,	3,	1,	50,	4,	0|(1<<MCID::Commutable), 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #757 = FMUL_D32
  { 758,	3,	1,	50,	4,	0|(1<<MCID::Commutable), 0x4ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #758 = FMUL_D64
  { 759,	3,	1,	50,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #759 = FMUL_MM
  { 760,	3,	1,	51,	4,	0|(1<<MCID::Commutable), 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #760 = FMUL_S
  { 761,	3,	1,	51,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #761 = FMUL_S_MM
  { 762,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #762 = FMUL_W
  { 763,	2,	1,	52,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #763 = FNEG_D32
  { 764,	2,	1,	52,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #764 = FNEG_D64
  { 765,	2,	1,	52,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #765 = FNEG_MM
  { 766,	2,	1,	52,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #766 = FNEG_S
  { 767,	2,	1,	52,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #767 = FNEG_S_MM
  { 768,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #768 = FRCP_D
  { 769,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #769 = FRCP_W
  { 770,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #770 = FRINT_D
  { 771,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #771 = FRINT_W
  { 772,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #772 = FRSQRT_D
  { 773,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #773 = FRSQRT_W
  { 774,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #774 = FSAF_D
  { 775,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #775 = FSAF_W
  { 776,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #776 = FSEQ_D
  { 777,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #777 = FSEQ_W
  { 778,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #778 = FSLE_D
  { 779,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #779 = FSLE_W
  { 780,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #780 = FSLT_D
  { 781,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #781 = FSLT_W
  { 782,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #782 = FSNE_D
  { 783,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #783 = FSNE_W
  { 784,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #784 = FSOR_D
  { 785,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #785 = FSOR_W
  { 786,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #786 = FSQRT_D
  { 787,	2,	1,	53,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #787 = FSQRT_D32
  { 788,	2,	1,	53,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #788 = FSQRT_D64
  { 789,	2,	1,	53,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo93,0,nullptr },  // Inst #789 = FSQRT_MM
  { 790,	2,	1,	54,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #790 = FSQRT_S
  { 791,	2,	1,	54,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #791 = FSQRT_S_MM
  { 792,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #792 = FSQRT_W
  { 793,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #793 = FSUB_D
  { 794,	3,	1,	55,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #794 = FSUB_D32
  { 795,	3,	1,	55,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #795 = FSUB_D64
  { 796,	3,	1,	55,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo117,0,nullptr },  // Inst #796 = FSUB_MM
  { 797,	3,	1,	56,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #797 = FSUB_S
  { 798,	3,	1,	56,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #798 = FSUB_S_MM
  { 799,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #799 = FSUB_W
  { 800,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #800 = FSUEQ_D
  { 801,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #801 = FSUEQ_W
  { 802,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #802 = FSULE_D
  { 803,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #803 = FSULE_W
  { 804,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #804 = FSULT_D
  { 805,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #805 = FSULT_W
  { 806,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #806 = FSUNE_D
  { 807,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #807 = FSUNE_W
  { 808,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #808 = FSUN_D
  { 809,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #809 = FSUN_W
  { 810,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #810 = FTINT_S_D
  { 811,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #811 = FTINT_S_W
  { 812,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #812 = FTINT_U_D
  { 813,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #813 = FTINT_U_W
  { 814,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo123,0,nullptr },  // Inst #814 = FTQ_H
  { 815,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo124,0,nullptr },  // Inst #815 = FTQ_W
  { 816,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #816 = FTRUNC_S_D
  { 817,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #817 = FTRUNC_S_W
  { 818,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #818 = FTRUNC_U_D
  { 819,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #819 = FTRUNC_U_W
  { 820,	4,	2,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo133,0,nullptr },  // Inst #820 = GotPrologue16
  { 821,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo101,0,nullptr },  // Inst #821 = HADD_S_D
  { 822,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo102,0,nullptr },  // Inst #822 = HADD_S_H
  { 823,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo103,0,nullptr },  // Inst #823 = HADD_S_W
  { 824,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo101,0,nullptr },  // Inst #824 = HADD_U_D
  { 825,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo102,0,nullptr },  // Inst #825 = HADD_U_H
  { 826,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo103,0,nullptr },  // Inst #826 = HADD_U_W
  { 827,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo101,0,nullptr },  // Inst #827 = HSUB_S_D
  { 828,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo102,0,nullptr },  // Inst #828 = HSUB_S_H
  { 829,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo103,0,nullptr },  // Inst #829 = HSUB_S_W
  { 830,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo101,0,nullptr },  // Inst #830 = HSUB_U_D
  { 831,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo102,0,nullptr },  // Inst #831 = HSUB_U_H
  { 832,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo103,0,nullptr },  // Inst #832 = HSUB_U_W
  { 833,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #833 = ILVEV_B
  { 834,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #834 = ILVEV_D
  { 835,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #835 = ILVEV_H
  { 836,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #836 = ILVEV_W
  { 837,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #837 = ILVL_B
  { 838,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #838 = ILVL_D
  { 839,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #839 = ILVL_H
  { 840,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #840 = ILVL_W
  { 841,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #841 = ILVOD_B
  { 842,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #842 = ILVOD_D
  { 843,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #843 = ILVOD_H
  { 844,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #844 = ILVOD_W
  { 845,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #845 = ILVR_B
  { 846,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #846 = ILVR_D
  { 847,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #847 = ILVR_H
  { 848,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #848 = ILVR_W
  { 849,	5,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo134,0,nullptr },  // Inst #849 = INS
  { 850,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo135,0,nullptr },  // Inst #850 = INSERT_B
  { 851,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo136,0,nullptr },  // Inst #851 = INSERT_B_VIDX_PSEUDO
  { 852,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo137,0,nullptr },  // Inst #852 = INSERT_D
  { 853,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo138,0,nullptr },  // Inst #853 = INSERT_D_VIDX_PSEUDO
  { 854,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo139,0,nullptr },  // Inst #854 = INSERT_FD_PSEUDO
  { 855,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo140,0,nullptr },  // Inst #855 = INSERT_FD_VIDX_PSEUDO
  { 856,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo141,0,nullptr },  // Inst #856 = INSERT_FW_PSEUDO
  { 857,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo142,0,nullptr },  // Inst #857 = INSERT_FW_VIDX_PSEUDO
  { 858,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo143,0,nullptr },  // Inst #858 = INSERT_H
  { 859,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo144,0,nullptr },  // Inst #859 = INSERT_H_VIDX_PSEUDO
  { 860,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo145,0,nullptr },  // Inst #860 = INSERT_W
  { 861,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo146,0,nullptr },  // Inst #861 = INSERT_W_VIDX_PSEUDO
  { 862,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, ImplicitList17, nullptr, OperandInfo147,0,nullptr },  // Inst #862 = INSV
  { 863,	5,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo148,0,nullptr },  // Inst #863 = INSVE_B
  { 864,	5,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo149,0,nullptr },  // Inst #864 = INSVE_D
  { 865,	5,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo150,0,nullptr },  // Inst #865 = INSVE_H
  { 866,	5,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo151,0,nullptr },  // Inst #866 = INSVE_W
  { 867,	5,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo134,0,nullptr },  // Inst #867 = INS_MM
  { 868,	1,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x3ULL, nullptr, ImplicitList4, OperandInfo5,0,nullptr },  // Inst #868 = J
  { 869,	1,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call), 0x3ULL, nullptr, ImplicitList5, OperandInfo5,0,nullptr },  // Inst #869 = JAL
  { 870,	2,	1,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList5, OperandInfo13,0,nullptr },  // Inst #870 = JALR
  { 871,	1,	0,	7,	2,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call), 0x0ULL, nullptr, ImplicitList5, OperandInfo65,0,nullptr },  // Inst #871 = JALR16_MM
  { 872,	2,	1,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList5, OperandInfo97,0,nullptr },  // Inst #872 = JALR64
  { 873,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::DelaySlot)|(1<<MCID::Call), 0x0ULL, nullptr, ImplicitList5, OperandInfo152,0,nullptr },  // Inst #873 = JALR64Pseudo
  { 874,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::DelaySlot)|(1<<MCID::Call), 0x0ULL, nullptr, ImplicitList5, OperandInfo65,0,nullptr },  // Inst #874 = JALRPseudo
  { 875,	1,	0,	7,	2,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList5, OperandInfo65,0,nullptr },  // Inst #875 = JALRS16_MM
  { 876,	2,	1,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList5, OperandInfo13,0,nullptr },  // Inst #876 = JALRS_MM
  { 877,	2,	1,	0,	4,	0|(1<<MCID::IndirectBranch)|(1<<MCID::DelaySlot)|(1<<MCID::UnmodeledSideEffects), 0x3ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #877 = JALR_HB
  { 878,	2,	1,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList5, OperandInfo13,0,nullptr },  // Inst #878 = JALR_MM
  { 879,	1,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x3ULL, nullptr, ImplicitList5, OperandInfo5,0,nullptr },  // Inst #879 = JALS_MM
  { 880,	1,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call), 0x3ULL, nullptr, ImplicitList5, OperandInfo5,0,nullptr },  // Inst #880 = JALX
  { 881,	1,	0,	7,	4,	0|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::UnmodeledSideEffects), 0x3ULL, nullptr, ImplicitList5, OperandInfo5,0,nullptr },  // Inst #881 = JAL_MM
  { 882,	2,	0,	0,	4,	0|(1<<MCID::Call)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList5, OperandInfo15,0,nullptr },  // Inst #882 = JIALC
  { 883,	2,	0,	0,	4,	0|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList4, OperandInfo15,0,nullptr },  // Inst #883 = JIC
  { 884,	1,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #884 = JR
  { 885,	1,	0,	7,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::DelaySlot)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #885 = JR16_MM
  { 886,	1,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo152,0,nullptr },  // Inst #886 = JR64
  { 887,	1,	0,	7,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #887 = JRADDIUSP
  { 888,	1,	0,	7,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #888 = JRC16_MM
  { 889,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x3ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #889 = JR_HB
  { 890,	1,	0,	0,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #890 = JR_HB_R6
  { 891,	1,	0,	7,	4,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #891 = JR_MM
  { 892,	1,	0,	7,	4,	0|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x3ULL, nullptr, ImplicitList4, OperandInfo5,0,nullptr },  // Inst #892 = J_MM
  { 893,	1,	0,	6,	6,	0|(1<<MCID::Call), 0x0ULL, nullptr, ImplicitList5, OperandInfo5,0,nullptr },  // Inst #893 = Jal16
  { 894,	1,	0,	6,	6,	0|(1<<MCID::Branch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList5, OperandInfo5,0,nullptr },  // Inst #894 = JalB16
  { 895,	0,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #895 = JrRa16
  { 896,	0,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #896 = JrcRa16
  { 897,	1,	0,	6,	2,	0|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo153,0,nullptr },  // Inst #897 = JrcRx16
  { 898,	1,	0,	7,	2,	0|(1<<MCID::Call), 0x0ULL, nullptr, ImplicitList5, OperandInfo153,0,nullptr },  // Inst #898 = JumpLinkReg16
  { 899,	3,	1,	57,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #899 = LB
  { 900,	3,	1,	57,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #900 = LB64
  { 901,	3,	1,	58,	2,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo156,0,nullptr },  // Inst #901 = LBU16_MM
  { 902,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo157,0,nullptr },  // Inst #902 = LBUX
  { 903,	3,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #903 = LB_MM
  { 904,	3,	1,	58,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #904 = LBu
  { 905,	3,	1,	58,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #905 = LBu64
  { 906,	3,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #906 = LBu_MM
  { 907,	3,	1,	59,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #907 = LD
  { 908,	3,	1,	60,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo158,0,nullptr },  // Inst #908 = LDC1
  { 909,	3,	1,	60,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo159,0,nullptr },  // Inst #909 = LDC164
  { 910,	3,	1,	60,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo158,0,nullptr },  // Inst #910 = LDC1_MM
  { 911,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #911 = LDC2
  { 912,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #912 = LDC2_R6
  { 913,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo161,0,nullptr },  // Inst #913 = LDC3
  { 914,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo162,0,nullptr },  // Inst #914 = LDI_B
  { 915,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo163,0,nullptr },  // Inst #915 = LDI_D
  { 916,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo164,0,nullptr },  // Inst #916 = LDI_H
  { 917,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo165,0,nullptr },  // Inst #917 = LDI_W
  { 918,	4,	1,	61,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo166,0,nullptr },  // Inst #918 = LDL
  { 919,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo167,0,nullptr },  // Inst #919 = LDPC
  { 920,	4,	1,	62,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo166,0,nullptr },  // Inst #920 = LDR
  { 921,	3,	1,	63,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo168,0,nullptr },  // Inst #921 = LDXC1
  { 922,	3,	1,	63,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo169,0,nullptr },  // Inst #922 = LDXC164
  { 923,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo170,0,nullptr },  // Inst #923 = LD_B
  { 924,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo171,0,nullptr },  // Inst #924 = LD_D
  { 925,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo172,0,nullptr },  // Inst #925 = LD_H
  { 926,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo173,0,nullptr },  // Inst #926 = LD_W
  { 927,	3,	1,	0,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #927 = LEA_ADDiu
  { 928,	3,	1,	0,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #928 = LEA_ADDiu64
  { 929,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #929 = LEA_ADDiu_MM
  { 930,	3,	1,	64,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #930 = LH
  { 931,	3,	1,	64,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #931 = LH64
  { 932,	3,	1,	65,	2,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo156,0,nullptr },  // Inst #932 = LHU16_MM
  { 933,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo157,0,nullptr },  // Inst #933 = LHX
  { 934,	3,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #934 = LH_MM
  { 935,	3,	1,	65,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #935 = LHu
  { 936,	3,	1,	65,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #936 = LHu64
  { 937,	3,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #937 = LHu_MM
  { 938,	2,	1,	0,	2,	0|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x0ULL, nullptr, nullptr, OperandInfo16,0,nullptr },  // Inst #938 = LI16_MM
  { 939,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #939 = LL
  { 940,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #940 = LLD
  { 941,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #941 = LLD_R6
  { 942,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo174,0,nullptr },  // Inst #942 = LL_MM
  { 943,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #943 = LL_R6
  { 944,	3,	1,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo175,0,nullptr },  // Inst #944 = LOAD_ACC128
  { 945,	3,	1,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo176,0,nullptr },  // Inst #945 = LOAD_ACC64
  { 946,	3,	1,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo177,0,nullptr },  // Inst #946 = LOAD_ACC64DSP
  { 947,	3,	1,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo178,0,nullptr },  // Inst #947 = LOAD_CCOND_DSP
  { 948,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo179,0,nullptr },  // Inst #948 = LONG_BRANCH_ADDiu
  { 949,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo180,0,nullptr },  // Inst #949 = LONG_BRANCH_DADDiu
  { 950,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo181,0,nullptr },  // Inst #950 = LONG_BRANCH_LUi
  { 951,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo30,0,nullptr },  // Inst #951 = LSA
  { 952,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo30,0,nullptr },  // Inst #952 = LSA_R6
  { 953,	3,	1,	66,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo168,0,nullptr },  // Inst #953 = LUXC1
  { 954,	3,	1,	66,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo169,0,nullptr },  // Inst #954 = LUXC164
  { 955,	3,	1,	66,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo168,0,nullptr },  // Inst #955 = LUXC1_MM
  { 956,	2,	1,	67,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x2ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #956 = LUi
  { 957,	2,	1,	67,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x2ULL, nullptr, nullptr, OperandInfo167,0,nullptr },  // Inst #957 = LUi64
  { 958,	2,	1,	67,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::CheapAsAMove), 0x2ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #958 = LUi_MM
  { 959,	3,	1,	68,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #959 = LW
  { 960,	3,	1,	68,	2,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo156,0,nullptr },  // Inst #960 = LW16_MM
  { 961,	3,	1,	68,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #961 = LW64
  { 962,	3,	1,	69,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo182,0,nullptr },  // Inst #962 = LWC1
  { 963,	3,	1,	69,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo182,0,nullptr },  // Inst #963 = LWC1_MM
  { 964,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #964 = LWC2
  { 965,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #965 = LWC2_R6
  { 966,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo161,0,nullptr },  // Inst #966 = LWC3
  { 967,	4,	1,	70,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo183,0,nullptr },  // Inst #967 = LWL
  { 968,	4,	1,	70,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo166,0,nullptr },  // Inst #968 = LWL64
  { 969,	4,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo184,0,nullptr },  // Inst #969 = LWL_MM
  { 970,	3,	1,	0,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo185,0,nullptr },  // Inst #970 = LWM16_MM
  { 971,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo185,0,nullptr },  // Inst #971 = LWM32_MM
  { 972,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #972 = LWPC
  { 973,	4,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo186,0,nullptr },  // Inst #973 = LWP_MM
  { 974,	4,	1,	71,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo183,0,nullptr },  // Inst #974 = LWR
  { 975,	4,	1,	71,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo166,0,nullptr },  // Inst #975 = LWR64
  { 976,	4,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo184,0,nullptr },  // Inst #976 = LWR_MM
  { 977,	3,	1,	68,	2,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo174,0,nullptr },  // Inst #977 = LWSP_MM
  { 978,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #978 = LWUPC
  { 979,	3,	1,	72,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo174,0,nullptr },  // Inst #979 = LWU_MM
  { 980,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo157,0,nullptr },  // Inst #980 = LWX
  { 981,	3,	1,	73,	4,	0|(1<<MCID::MayLoad), 0x5ULL, nullptr, nullptr, OperandInfo187,0,nullptr },  // Inst #981 = LWXC1
  { 982,	3,	1,	73,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo187,0,nullptr },  // Inst #982 = LWXC1_MM
  { 983,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo157,0,nullptr },  // Inst #983 = LWXS_MM
  { 984,	3,	1,	0,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #984 = LW_MM
  { 985,	3,	1,	72,	4,	0|(1<<MCID::FoldableAsLoad)|(1<<MCID::MayLoad), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #985 = LWu
  { 986,	4,	1,	57,	4,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #986 = LbRxRyOffMemX16
  { 987,	4,	1,	58,	4,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #987 = LbuRxRyOffMemX16
  { 988,	4,	1,	64,	4,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #988 = LhRxRyOffMemX16
  { 989,	4,	1,	65,	4,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #989 = LhuRxRyOffMemX16
  { 990,	2,	1,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo39,0,nullptr },  // Inst #990 = LiRxImm16
  { 991,	2,	1,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo39,0,nullptr },  // Inst #991 = LiRxImmAlignX16
  { 992,	2,	1,	6,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo39,0,nullptr },  // Inst #992 = LiRxImmX16
  { 993,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #993 = LoadAddr32Imm
  { 994,	3,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #994 = LoadAddr32Reg
  { 995,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #995 = LoadImm32Reg
  { 996,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo167,0,nullptr },  // Inst #996 = LoadImm64Reg
  { 997,	3,	1,	3,	2,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo189,0,nullptr },  // Inst #997 = LwConstant32
  { 998,	3,	1,	68,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo190,0,nullptr },  // Inst #998 = LwRxPcTcp16
  { 999,	3,	1,	68,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo190,0,nullptr },  // Inst #999 = LwRxPcTcpX16
  { 1000,	4,	1,	68,	4,	0|(1<<MCID::MayLoad), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #1000 = LwRxRyOffMemX16
  { 1001,	3,	1,	68,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, nullptr, OperandInfo191,0,nullptr },  // Inst #1001 = LwRxSpImmX16
  { 1002,	2,	0,	74,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1002 = MADD
  { 1003,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo192,0,nullptr },  // Inst #1003 = MADDF_D
  { 1004,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo193,0,nullptr },  // Inst #1004 = MADDF_S
  { 1005,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1005 = MADDR_Q_H
  { 1006,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1006 = MADDR_Q_W
  { 1007,	2,	0,	75,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1007 = MADDU
  { 1008,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #1008 = MADDU_DSP
  { 1009,	2,	0,	75,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1009 = MADDU_MM
  { 1010,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #1010 = MADDV_B
  { 1011,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #1011 = MADDV_D
  { 1012,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1012 = MADDV_H
  { 1013,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1013 = MADDV_W
  { 1014,	4,	1,	76,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1014 = MADD_D32
  { 1015,	4,	1,	76,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1015 = MADD_D32_MM
  { 1016,	4,	1,	76,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo195,0,nullptr },  // Inst #1016 = MADD_D64
  { 1017,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #1017 = MADD_DSP
  { 1018,	2,	0,	74,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1018 = MADD_MM
  { 1019,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1019 = MADD_Q_H
  { 1020,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1020 = MADD_Q_W
  { 1021,	4,	1,	77,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1021 = MADD_S
  { 1022,	4,	1,	77,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1022 = MADD_S_MM
  { 1023,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #1023 = MAQ_SA_W_PHL
  { 1024,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #1024 = MAQ_SA_W_PHR
  { 1025,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #1025 = MAQ_S_W_PHL
  { 1026,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #1026 = MAQ_S_W_PHR
  { 1027,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #1027 = MAXA_D
  { 1028,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #1028 = MAXA_S
  { 1029,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1029 = MAXI_S_B
  { 1030,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1030 = MAXI_S_D
  { 1031,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1031 = MAXI_S_H
  { 1032,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1032 = MAXI_S_W
  { 1033,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1033 = MAXI_U_B
  { 1034,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1034 = MAXI_U_D
  { 1035,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1035 = MAXI_U_H
  { 1036,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1036 = MAXI_U_W
  { 1037,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1037 = MAX_A_B
  { 1038,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1038 = MAX_A_D
  { 1039,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1039 = MAX_A_H
  { 1040,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1040 = MAX_A_W
  { 1041,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #1041 = MAX_D
  { 1042,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #1042 = MAX_S
  { 1043,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1043 = MAX_S_B
  { 1044,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1044 = MAX_S_D
  { 1045,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1045 = MAX_S_H
  { 1046,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1046 = MAX_S_W
  { 1047,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1047 = MAX_U_B
  { 1048,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1048 = MAX_U_D
  { 1049,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1049 = MAX_U_H
  { 1050,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1050 = MAX_U_W
  { 1051,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1051 = MFC0
  { 1052,	2,	1,	78,	4,	0|(1<<MCID::Bitcast), 0x4ULL, nullptr, nullptr, OperandInfo197,0,nullptr },  // Inst #1052 = MFC1
  { 1053,	2,	1,	78,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo197,0,nullptr },  // Inst #1053 = MFC1_MM
  { 1054,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1054 = MFC2
  { 1055,	2,	1,	79,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo198,0,nullptr },  // Inst #1055 = MFHC1_D32
  { 1056,	2,	1,	79,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo199,0,nullptr },  // Inst #1056 = MFHC1_D64
  { 1057,	2,	1,	79,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo198,0,nullptr },  // Inst #1057 = MFHC1_MM
  { 1058,	1,	1,	80,	4,	0, 0x1ULL, ImplicitList18, nullptr, OperandInfo65,0,nullptr },  // Inst #1058 = MFHI
  { 1059,	1,	1,	80,	2,	0, 0x0ULL, ImplicitList18, nullptr, OperandInfo65,0,nullptr },  // Inst #1059 = MFHI16_MM
  { 1060,	1,	1,	80,	4,	0, 0x1ULL, ImplicitList19, nullptr, OperandInfo152,0,nullptr },  // Inst #1060 = MFHI64
  { 1061,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo200,0,nullptr },  // Inst #1061 = MFHI_DSP
  { 1062,	1,	1,	80,	4,	0, 0x1ULL, ImplicitList18, nullptr, OperandInfo65,0,nullptr },  // Inst #1062 = MFHI_MM
  { 1063,	1,	1,	80,	4,	0, 0x1ULL, ImplicitList18, nullptr, OperandInfo65,0,nullptr },  // Inst #1063 = MFLO
  { 1064,	1,	1,	80,	2,	0, 0x0ULL, ImplicitList18, nullptr, OperandInfo65,0,nullptr },  // Inst #1064 = MFLO16_MM
  { 1065,	1,	1,	80,	4,	0, 0x1ULL, ImplicitList19, nullptr, OperandInfo152,0,nullptr },  // Inst #1065 = MFLO64
  { 1066,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo200,0,nullptr },  // Inst #1066 = MFLO_DSP
  { 1067,	1,	1,	80,	4,	0, 0x1ULL, ImplicitList18, nullptr, OperandInfo65,0,nullptr },  // Inst #1067 = MFLO_MM
  { 1068,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #1068 = MINA_D
  { 1069,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #1069 = MINA_S
  { 1070,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1070 = MINI_S_B
  { 1071,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1071 = MINI_S_D
  { 1072,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1072 = MINI_S_H
  { 1073,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1073 = MINI_S_W
  { 1074,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1074 = MINI_U_B
  { 1075,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1075 = MINI_U_D
  { 1076,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1076 = MINI_U_H
  { 1077,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1077 = MINI_U_W
  { 1078,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1078 = MIN_A_B
  { 1079,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1079 = MIN_A_D
  { 1080,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1080 = MIN_A_H
  { 1081,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1081 = MIN_A_W
  { 1082,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #1082 = MIN_D
  { 1083,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #1083 = MIN_S
  { 1084,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1084 = MIN_S_B
  { 1085,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1085 = MIN_S_D
  { 1086,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1086 = MIN_S_H
  { 1087,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1087 = MIN_S_W
  { 1088,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1088 = MIN_U_B
  { 1089,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1089 = MIN_U_D
  { 1090,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1090 = MIN_U_H
  { 1091,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1091 = MIN_U_W
  { 1092,	2,	0,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, ImplicitList20, nullptr, OperandInfo13,0,nullptr },  // Inst #1092 = MIPSeh_return32
  { 1093,	2,	0,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::Terminator), 0x0ULL, ImplicitList20, nullptr, OperandInfo97,0,nullptr },  // Inst #1093 = MIPSeh_return64
  { 1094,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1094 = MOD
  { 1095,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1095 = MODSUB
  { 1096,	3,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1096 = MODU
  { 1097,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1097 = MOD_S_B
  { 1098,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1098 = MOD_S_D
  { 1099,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1099 = MOD_S_H
  { 1100,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1100 = MOD_S_W
  { 1101,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1101 = MOD_U_B
  { 1102,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1102 = MOD_U_D
  { 1103,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1103 = MOD_U_H
  { 1104,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1104 = MOD_U_W
  { 1105,	2,	1,	0,	2,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1105 = MOVE16_MM
  { 1106,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo201,0,nullptr },  // Inst #1106 = MOVE_V
  { 1107,	4,	1,	81,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo202,0,nullptr },  // Inst #1107 = MOVF_D32
  { 1108,	4,	1,	81,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo202,0,nullptr },  // Inst #1108 = MOVF_D32_MM
  { 1109,	4,	1,	81,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo203,0,nullptr },  // Inst #1109 = MOVF_D64
  { 1110,	4,	1,	82,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo204,0,nullptr },  // Inst #1110 = MOVF_I
  { 1111,	4,	1,	82,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo205,0,nullptr },  // Inst #1111 = MOVF_I64
  { 1112,	4,	1,	82,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo204,0,nullptr },  // Inst #1112 = MOVF_I_MM
  { 1113,	4,	1,	83,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo206,0,nullptr },  // Inst #1113 = MOVF_S
  { 1114,	4,	1,	83,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo206,0,nullptr },  // Inst #1114 = MOVF_S_MM
  { 1115,	4,	1,	84,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo207,0,nullptr },  // Inst #1115 = MOVN_I64_D64
  { 1116,	4,	1,	85,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo208,0,nullptr },  // Inst #1116 = MOVN_I64_I
  { 1117,	4,	1,	85,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo209,0,nullptr },  // Inst #1117 = MOVN_I64_I64
  { 1118,	4,	1,	86,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo210,0,nullptr },  // Inst #1118 = MOVN_I64_S
  { 1119,	4,	1,	84,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo211,0,nullptr },  // Inst #1119 = MOVN_I_D32
  { 1120,	4,	1,	84,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo211,0,nullptr },  // Inst #1120 = MOVN_I_D32_MM
  { 1121,	4,	1,	84,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo212,0,nullptr },  // Inst #1121 = MOVN_I_D64
  { 1122,	4,	1,	85,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo213,0,nullptr },  // Inst #1122 = MOVN_I_I
  { 1123,	4,	1,	85,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo214,0,nullptr },  // Inst #1123 = MOVN_I_I64
  { 1124,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo213,0,nullptr },  // Inst #1124 = MOVN_I_MM
  { 1125,	4,	1,	86,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo215,0,nullptr },  // Inst #1125 = MOVN_I_S
  { 1126,	4,	1,	86,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo215,0,nullptr },  // Inst #1126 = MOVN_I_S_MM
  { 1127,	4,	1,	87,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo202,0,nullptr },  // Inst #1127 = MOVT_D32
  { 1128,	4,	1,	87,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo202,0,nullptr },  // Inst #1128 = MOVT_D32_MM
  { 1129,	4,	1,	87,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo203,0,nullptr },  // Inst #1129 = MOVT_D64
  { 1130,	4,	1,	88,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo204,0,nullptr },  // Inst #1130 = MOVT_I
  { 1131,	4,	1,	88,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo205,0,nullptr },  // Inst #1131 = MOVT_I64
  { 1132,	4,	1,	88,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo204,0,nullptr },  // Inst #1132 = MOVT_I_MM
  { 1133,	4,	1,	89,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo206,0,nullptr },  // Inst #1133 = MOVT_S
  { 1134,	4,	1,	89,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo206,0,nullptr },  // Inst #1134 = MOVT_S_MM
  { 1135,	4,	1,	90,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo207,0,nullptr },  // Inst #1135 = MOVZ_I64_D64
  { 1136,	4,	1,	91,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo208,0,nullptr },  // Inst #1136 = MOVZ_I64_I
  { 1137,	4,	1,	91,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo209,0,nullptr },  // Inst #1137 = MOVZ_I64_I64
  { 1138,	4,	1,	92,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo210,0,nullptr },  // Inst #1138 = MOVZ_I64_S
  { 1139,	4,	1,	90,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo211,0,nullptr },  // Inst #1139 = MOVZ_I_D32
  { 1140,	4,	1,	90,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo211,0,nullptr },  // Inst #1140 = MOVZ_I_D32_MM
  { 1141,	4,	1,	90,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo212,0,nullptr },  // Inst #1141 = MOVZ_I_D64
  { 1142,	4,	1,	91,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo213,0,nullptr },  // Inst #1142 = MOVZ_I_I
  { 1143,	4,	1,	91,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo214,0,nullptr },  // Inst #1143 = MOVZ_I_I64
  { 1144,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo213,0,nullptr },  // Inst #1144 = MOVZ_I_MM
  { 1145,	4,	1,	92,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo215,0,nullptr },  // Inst #1145 = MOVZ_I_S
  { 1146,	4,	1,	92,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo215,0,nullptr },  // Inst #1146 = MOVZ_I_S_MM
  { 1147,	2,	0,	93,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1147 = MSUB
  { 1148,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo192,0,nullptr },  // Inst #1148 = MSUBF_D
  { 1149,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo193,0,nullptr },  // Inst #1149 = MSUBF_S
  { 1150,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1150 = MSUBR_Q_H
  { 1151,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1151 = MSUBR_Q_W
  { 1152,	2,	0,	94,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1152 = MSUBU
  { 1153,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #1153 = MSUBU_DSP
  { 1154,	2,	0,	94,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1154 = MSUBU_MM
  { 1155,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #1155 = MSUBV_B
  { 1156,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #1156 = MSUBV_D
  { 1157,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1157 = MSUBV_H
  { 1158,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1158 = MSUBV_W
  { 1159,	4,	1,	95,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1159 = MSUB_D32
  { 1160,	4,	1,	95,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1160 = MSUB_D32_MM
  { 1161,	4,	1,	95,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo195,0,nullptr },  // Inst #1161 = MSUB_D64
  { 1162,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #1162 = MSUB_DSP
  { 1163,	2,	0,	93,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, ImplicitList12, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1163 = MSUB_MM
  { 1164,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1164 = MSUB_Q_H
  { 1165,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1165 = MSUB_Q_W
  { 1166,	4,	1,	96,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1166 = MSUB_S
  { 1167,	4,	1,	96,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1167 = MSUB_S_MM
  { 1168,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1168 = MTC0
  { 1169,	2,	1,	97,	4,	0|(1<<MCID::Bitcast), 0x4ULL, nullptr, nullptr, OperandInfo216,0,nullptr },  // Inst #1169 = MTC1
  { 1170,	2,	1,	97,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo216,0,nullptr },  // Inst #1170 = MTC1_MM
  { 1171,	3,	3,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1171 = MTC2
  { 1172,	3,	1,	98,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo217,0,nullptr },  // Inst #1172 = MTHC1_D32
  { 1173,	3,	1,	98,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo218,0,nullptr },  // Inst #1173 = MTHC1_D64
  { 1174,	3,	1,	98,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo217,0,nullptr },  // Inst #1174 = MTHC1_MM
  { 1175,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList21, OperandInfo65,0,nullptr },  // Inst #1175 = MTHI
  { 1176,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList22, OperandInfo152,0,nullptr },  // Inst #1176 = MTHI64
  { 1177,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo219,0,nullptr },  // Inst #1177 = MTHI_DSP
  { 1178,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList21, OperandInfo65,0,nullptr },  // Inst #1178 = MTHI_MM
  { 1179,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList6, OperandInfo220,0,nullptr },  // Inst #1179 = MTHLIP
  { 1180,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList23, OperandInfo65,0,nullptr },  // Inst #1180 = MTLO
  { 1181,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList24, OperandInfo152,0,nullptr },  // Inst #1181 = MTLO64
  { 1182,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo221,0,nullptr },  // Inst #1182 = MTLO_DSP
  { 1183,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList23, OperandInfo65,0,nullptr },  // Inst #1183 = MTLO_MM
  { 1184,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList25, OperandInfo152,0,nullptr },  // Inst #1184 = MTM0
  { 1185,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList26, OperandInfo152,0,nullptr },  // Inst #1185 = MTM1
  { 1186,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList27, OperandInfo152,0,nullptr },  // Inst #1186 = MTM2
  { 1187,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList28, OperandInfo152,0,nullptr },  // Inst #1187 = MTP0
  { 1188,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList29, OperandInfo152,0,nullptr },  // Inst #1188 = MTP1
  { 1189,	1,	0,	99,	4,	0, 0x1ULL, nullptr, ImplicitList30, OperandInfo152,0,nullptr },  // Inst #1189 = MTP2
  { 1190,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1190 = MUH
  { 1191,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1191 = MUHU
  { 1192,	3,	1,	100,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, ImplicitList12, OperandInfo14,0,nullptr },  // Inst #1192 = MUL
  { 1193,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo81,0,nullptr },  // Inst #1193 = MULEQ_S_W_PHL
  { 1194,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo81,0,nullptr },  // Inst #1194 = MULEQ_S_W_PHR
  { 1195,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo19,0,nullptr },  // Inst #1195 = MULEU_S_PH_QBL
  { 1196,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo19,0,nullptr },  // Inst #1196 = MULEU_S_PH_QBR
  { 1197,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo19,0,nullptr },  // Inst #1197 = MULQ_RS_PH
  { 1198,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo14,0,nullptr },  // Inst #1198 = MULQ_RS_W
  { 1199,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo19,0,nullptr },  // Inst #1199 = MULQ_S_PH
  { 1200,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo14,0,nullptr },  // Inst #1200 = MULQ_S_W
  { 1201,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1201 = MULR_Q_H
  { 1202,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1202 = MULR_Q_W
  { 1203,	4,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList11, OperandInfo107,0,nullptr },  // Inst #1203 = MULSAQ_S_W_PH
  { 1204,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo107,0,nullptr },  // Inst #1204 = MULSA_W_PH
  { 1205,	2,	0,	101,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1205 = MULT
  { 1206,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo222,0,nullptr },  // Inst #1206 = MULTU_DSP
  { 1207,	3,	1,	0,	4,	0|(1<<MCID::Commutable), 0x6ULL, nullptr, nullptr, OperandInfo222,0,nullptr },  // Inst #1207 = MULT_DSP
  { 1208,	2,	0,	101,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1208 = MULT_MM
  { 1209,	2,	0,	102,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1209 = MULTu
  { 1210,	2,	0,	102,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1210 = MULTu_MM
  { 1211,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1211 = MULU
  { 1212,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1212 = MULV_B
  { 1213,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1213 = MULV_D
  { 1214,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1214 = MULV_H
  { 1215,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1215 = MULV_W
  { 1216,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1216 = MUL_MM
  { 1217,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo19,0,nullptr },  // Inst #1217 = MUL_PH
  { 1218,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1218 = MUL_Q_H
  { 1219,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1219 = MUL_Q_W
  { 1220,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1220 = MUL_R6
  { 1221,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList31, OperandInfo19,0,nullptr },  // Inst #1221 = MUL_S_PH
  { 1222,	1,	1,	6,	2,	0, 0x0ULL, ImplicitList21, nullptr, OperandInfo153,0,nullptr },  // Inst #1222 = Mfhi16
  { 1223,	1,	1,	6,	2,	0, 0x0ULL, ImplicitList23, nullptr, OperandInfo153,0,nullptr },  // Inst #1223 = Mflo16
  { 1224,	2,	1,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo223,0,nullptr },  // Inst #1224 = Move32R16
  { 1225,	2,	1,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo224,0,nullptr },  // Inst #1225 = MoveR3216
  { 1226,	2,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, ImplicitList12, OperandInfo94,0,nullptr },  // Inst #1226 = MultRxRy16
  { 1227,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, ImplicitList12, OperandInfo42,0,nullptr },  // Inst #1227 = MultRxRyRz16
  { 1228,	2,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, ImplicitList12, OperandInfo94,0,nullptr },  // Inst #1228 = MultuRxRy16
  { 1229,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, ImplicitList12, OperandInfo42,0,nullptr },  // Inst #1229 = MultuRxRyRz16
  { 1230,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo201,0,nullptr },  // Inst #1230 = NLOC_B
  { 1231,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #1231 = NLOC_D
  { 1232,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo225,0,nullptr },  // Inst #1232 = NLOC_H
  { 1233,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #1233 = NLOC_W
  { 1234,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo201,0,nullptr },  // Inst #1234 = NLZC_B
  { 1235,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #1235 = NLZC_D
  { 1236,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo225,0,nullptr },  // Inst #1236 = NLZC_H
  { 1237,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #1237 = NLZC_W
  { 1238,	4,	1,	103,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1238 = NMADD_D32
  { 1239,	4,	1,	103,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1239 = NMADD_D32_MM
  { 1240,	4,	1,	103,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo195,0,nullptr },  // Inst #1240 = NMADD_D64
  { 1241,	4,	1,	104,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1241 = NMADD_S
  { 1242,	4,	1,	104,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1242 = NMADD_S_MM
  { 1243,	4,	1,	105,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1243 = NMSUB_D32
  { 1244,	4,	1,	105,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo194,0,nullptr },  // Inst #1244 = NMSUB_D32_MM
  { 1245,	4,	1,	105,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo195,0,nullptr },  // Inst #1245 = NMSUB_D64
  { 1246,	4,	1,	106,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1246 = NMSUB_S
  { 1247,	4,	1,	106,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x4ULL, nullptr, nullptr, OperandInfo196,0,nullptr },  // Inst #1247 = NMSUB_S_MM
  { 1248,	0,	0,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1248 = NOP
  { 1249,	3,	1,	107,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1249 = NOR
  { 1250,	3,	1,	107,	4,	0|(1<<MCID::Commutable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1250 = NOR64
  { 1251,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1251 = NORI_B
  { 1252,	3,	1,	107,	4,	0|(1<<MCID::Commutable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1252 = NOR_MM
  { 1253,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1253 = NOR_V
  { 1254,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1254 = NOR_V_D_PSEUDO
  { 1255,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1255 = NOR_V_H_PSEUDO
  { 1256,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1256 = NOR_V_W_PSEUDO
  { 1257,	2,	1,	0,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo226,0,nullptr },  // Inst #1257 = NOT16_MM
  { 1258,	2,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo94,0,nullptr },  // Inst #1258 = NegRxRy16
  { 1259,	2,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo94,0,nullptr },  // Inst #1259 = NotRxRy16
  { 1260,	3,	1,	108,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1260 = OR
  { 1261,	3,	1,	108,	2,	0|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo31,0,nullptr },  // Inst #1261 = OR16_MM
  { 1262,	3,	1,	108,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1262 = OR64
  { 1263,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1263 = ORI_B
  { 1264,	3,	1,	108,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1264 = OR_MM
  { 1265,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1265 = OR_V
  { 1266,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1266 = OR_V_D_PSEUDO
  { 1267,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1267 = OR_V_H_PSEUDO
  { 1268,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1268 = OR_V_W_PSEUDO
  { 1269,	3,	1,	109,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1269 = ORi
  { 1270,	3,	1,	108,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #1270 = ORi64
  { 1271,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1271 = ORi_MM
  { 1272,	3,	1,	6,	2,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo43,0,nullptr },  // Inst #1272 = OrRxRxRy16
  { 1273,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1273 = PACKRL_PH
  { 1274,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1274 = PAUSE
  { 1275,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1275 = PAUSE_MM
  { 1276,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1276 = PCKEV_B
  { 1277,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1277 = PCKEV_D
  { 1278,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1278 = PCKEV_H
  { 1279,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1279 = PCKEV_W
  { 1280,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1280 = PCKOD_B
  { 1281,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1281 = PCKOD_D
  { 1282,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1282 = PCKOD_H
  { 1283,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1283 = PCKOD_W
  { 1284,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo201,0,nullptr },  // Inst #1284 = PCNT_B
  { 1285,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo115,0,nullptr },  // Inst #1285 = PCNT_D
  { 1286,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo225,0,nullptr },  // Inst #1286 = PCNT_H
  { 1287,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo116,0,nullptr },  // Inst #1287 = PCNT_W
  { 1288,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, ImplicitList8, nullptr, OperandInfo19,0,nullptr },  // Inst #1288 = PICK_PH
  { 1289,	3,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, ImplicitList8, nullptr, OperandInfo19,0,nullptr },  // Inst #1289 = PICK_QB
  { 1290,	2,	1,	25,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1290 = POP
  { 1291,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1291 = PRECEQU_PH_QBL
  { 1292,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1292 = PRECEQU_PH_QBLA
  { 1293,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1293 = PRECEQU_PH_QBR
  { 1294,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1294 = PRECEQU_PH_QBRA
  { 1295,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo227,0,nullptr },  // Inst #1295 = PRECEQ_W_PHL
  { 1296,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo227,0,nullptr },  // Inst #1296 = PRECEQ_W_PHR
  { 1297,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1297 = PRECEU_PH_QBL
  { 1298,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1298 = PRECEU_PH_QBLA
  { 1299,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1299 = PRECEU_PH_QBR
  { 1300,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo12,0,nullptr },  // Inst #1300 = PRECEU_PH_QBRA
  { 1301,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo19,0,nullptr },  // Inst #1301 = PRECRQU_S_QB_PH
  { 1302,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo228,0,nullptr },  // Inst #1302 = PRECRQ_PH_W
  { 1303,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1303 = PRECRQ_QB_PH
  { 1304,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo228,0,nullptr },  // Inst #1304 = PRECRQ_RS_PH_W
  { 1305,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1305 = PRECR_QB_PH
  { 1306,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo229,0,nullptr },  // Inst #1306 = PRECR_SRA_PH_W
  { 1307,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo229,0,nullptr },  // Inst #1307 = PRECR_SRA_R_PH_W
  { 1308,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo71,0,nullptr },  // Inst #1308 = PREF
  { 1309,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo72,0,nullptr },  // Inst #1309 = PREF_MM
  { 1310,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo71,0,nullptr },  // Inst #1310 = PREF_R6
  { 1311,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo34,0,nullptr },  // Inst #1311 = PREPEND
  { 1312,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo230,0,nullptr },  // Inst #1312 = PseudoCMPU_EQ_QB
  { 1313,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo230,0,nullptr },  // Inst #1313 = PseudoCMPU_LE_QB
  { 1314,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo230,0,nullptr },  // Inst #1314 = PseudoCMPU_LT_QB
  { 1315,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo230,0,nullptr },  // Inst #1315 = PseudoCMP_EQ_PH
  { 1316,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo230,0,nullptr },  // Inst #1316 = PseudoCMP_LE_PH
  { 1317,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo230,0,nullptr },  // Inst #1317 = PseudoCMP_LT_PH
  { 1318,	2,	1,	14,	4,	0|(1<<MCID::Pseudo), 0x4ULL, nullptr, nullptr, OperandInfo231,0,nullptr },  // Inst #1318 = PseudoCVT_D32_W
  { 1319,	2,	1,	14,	4,	0|(1<<MCID::Pseudo), 0x4ULL, nullptr, nullptr, OperandInfo100,0,nullptr },  // Inst #1319 = PseudoCVT_D64_L
  { 1320,	2,	1,	14,	4,	0|(1<<MCID::Pseudo), 0x4ULL, nullptr, nullptr, OperandInfo232,0,nullptr },  // Inst #1320 = PseudoCVT_D64_W
  { 1321,	2,	1,	14,	4,	0|(1<<MCID::Pseudo), 0x4ULL, nullptr, nullptr, OperandInfo100,0,nullptr },  // Inst #1321 = PseudoCVT_S_L
  { 1322,	2,	1,	14,	4,	0|(1<<MCID::Pseudo), 0x4ULL, nullptr, nullptr, OperandInfo216,0,nullptr },  // Inst #1322 = PseudoCVT_S_W
  { 1323,	3,	1,	23,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo233,0,nullptr },  // Inst #1323 = PseudoDMULT
  { 1324,	3,	1,	24,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo233,0,nullptr },  // Inst #1324 = PseudoDMULTu
  { 1325,	3,	1,	29,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo233,0,nullptr },  // Inst #1325 = PseudoDSDIV
  { 1326,	3,	1,	41,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo233,0,nullptr },  // Inst #1326 = PseudoDUDIV
  { 1327,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #1327 = PseudoIndirectBranch
  { 1328,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Branch)|(1<<MCID::IndirectBranch)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, OperandInfo152,0,nullptr },  // Inst #1328 = PseudoIndirectBranch64
  { 1329,	4,	1,	74,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo234,0,nullptr },  // Inst #1329 = PseudoMADD
  { 1330,	4,	1,	75,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo234,0,nullptr },  // Inst #1330 = PseudoMADDU
  { 1331,	2,	1,	80,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo235,0,nullptr },  // Inst #1331 = PseudoMFHI
  { 1332,	2,	1,	80,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo236,0,nullptr },  // Inst #1332 = PseudoMFHI64
  { 1333,	2,	1,	80,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo235,0,nullptr },  // Inst #1333 = PseudoMFLO
  { 1334,	2,	1,	80,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo236,0,nullptr },  // Inst #1334 = PseudoMFLO64
  { 1335,	4,	1,	93,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo234,0,nullptr },  // Inst #1335 = PseudoMSUB
  { 1336,	4,	1,	94,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo234,0,nullptr },  // Inst #1336 = PseudoMSUBU
  { 1337,	3,	1,	99,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo237,0,nullptr },  // Inst #1337 = PseudoMTLOHI
  { 1338,	3,	1,	99,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo233,0,nullptr },  // Inst #1338 = PseudoMTLOHI64
  { 1339,	3,	1,	99,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo222,0,nullptr },  // Inst #1339 = PseudoMTLOHI_DSP
  { 1340,	3,	1,	101,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo237,0,nullptr },  // Inst #1340 = PseudoMULT
  { 1341,	3,	1,	102,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo237,0,nullptr },  // Inst #1341 = PseudoMULTu
  { 1342,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo238,0,nullptr },  // Inst #1342 = PseudoPICK_PH
  { 1343,	4,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo238,0,nullptr },  // Inst #1343 = PseudoPICK_QB
  { 1344,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects)|(1<<MCID::ExtraSrcRegAllocReq), 0x0ULL, nullptr, nullptr, OperandInfo65,0,nullptr },  // Inst #1344 = PseudoReturn
  { 1345,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects)|(1<<MCID::ExtraSrcRegAllocReq), 0x0ULL, nullptr, nullptr, OperandInfo152,0,nullptr },  // Inst #1345 = PseudoReturn64
  { 1346,	3,	1,	110,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo237,0,nullptr },  // Inst #1346 = PseudoSDIV
  { 1347,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo239,0,nullptr },  // Inst #1347 = PseudoSELECTFP_F_D32
  { 1348,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo240,0,nullptr },  // Inst #1348 = PseudoSELECTFP_F_D64
  { 1349,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo241,0,nullptr },  // Inst #1349 = PseudoSELECTFP_F_I
  { 1350,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo242,0,nullptr },  // Inst #1350 = PseudoSELECTFP_F_I64
  { 1351,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo243,0,nullptr },  // Inst #1351 = PseudoSELECTFP_F_S
  { 1352,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo239,0,nullptr },  // Inst #1352 = PseudoSELECTFP_T_D32
  { 1353,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo240,0,nullptr },  // Inst #1353 = PseudoSELECTFP_T_D64
  { 1354,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo241,0,nullptr },  // Inst #1354 = PseudoSELECTFP_T_I
  { 1355,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo242,0,nullptr },  // Inst #1355 = PseudoSELECTFP_T_I64
  { 1356,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo243,0,nullptr },  // Inst #1356 = PseudoSELECTFP_T_S
  { 1357,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo239,0,nullptr },  // Inst #1357 = PseudoSELECT_D32
  { 1358,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo240,0,nullptr },  // Inst #1358 = PseudoSELECT_D64
  { 1359,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo241,0,nullptr },  // Inst #1359 = PseudoSELECT_I
  { 1360,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo242,0,nullptr },  // Inst #1360 = PseudoSELECT_I64
  { 1361,	4,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo243,0,nullptr },  // Inst #1361 = PseudoSELECT_S
  { 1362,	3,	1,	111,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo237,0,nullptr },  // Inst #1362 = PseudoUDIV
  { 1363,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo227,0,nullptr },  // Inst #1363 = RADDU_W_QB
  { 1364,	2,	1,	0,	4,	0|(1<<MCID::MayLoad), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1364 = RDDSP
  { 1365,	2,	1,	112,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo244,0,nullptr },  // Inst #1365 = RDHWR
  { 1366,	2,	1,	112,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo245,0,nullptr },  // Inst #1366 = RDHWR64
  { 1367,	2,	1,	112,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo244,0,nullptr },  // Inst #1367 = RDHWR_MM
  { 1368,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo246,0,nullptr },  // Inst #1368 = REPLV_PH
  { 1369,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo246,0,nullptr },  // Inst #1369 = REPLV_QB
  { 1370,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo247,0,nullptr },  // Inst #1370 = REPL_PH
  { 1371,	2,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo247,0,nullptr },  // Inst #1371 = REPL_QB
  { 1372,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #1372 = RINT_D
  { 1373,	2,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #1373 = RINT_S
  { 1374,	3,	1,	113,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1374 = ROTR
  { 1375,	3,	1,	114,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1375 = ROTRV
  { 1376,	3,	1,	114,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1376 = ROTRV_MM
  { 1377,	3,	1,	113,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1377 = ROTR_MM
  { 1378,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #1378 = ROUND_L_D64
  { 1379,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #1379 = ROUND_L_S
  { 1380,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #1380 = ROUND_W_D32
  { 1381,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #1381 = ROUND_W_D64
  { 1382,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #1382 = ROUND_W_MM
  { 1383,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #1383 = ROUND_W_S
  { 1384,	2,	1,	115,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #1384 = ROUND_W_S_MM
  { 1385,	0,	0,	116,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, nullptr,0,nullptr },  // Inst #1385 = Restore16
  { 1386,	0,	0,	116,	2,	0|(1<<MCID::MayLoad)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, nullptr,0,nullptr },  // Inst #1386 = RestoreX16
  { 1387,	0,	0,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1387 = RetRA
  { 1388,	0,	0,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Terminator)|(1<<MCID::ExtraSrcRegAllocReq), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1388 = RetRA16
  { 1389,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1389 = SAT_S_B
  { 1390,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1390 = SAT_S_D
  { 1391,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1391 = SAT_S_H
  { 1392,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1392 = SAT_S_W
  { 1393,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1393 = SAT_U_B
  { 1394,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1394 = SAT_U_D
  { 1395,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1395 = SAT_U_H
  { 1396,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1396 = SAT_U_W
  { 1397,	3,	0,	117,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1397 = SB
  { 1398,	3,	0,	117,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo248,0,nullptr },  // Inst #1398 = SB16_MM
  { 1399,	3,	0,	117,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1399 = SB64
  { 1400,	3,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1400 = SB_MM
  { 1401,	4,	1,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo249,0,nullptr },  // Inst #1401 = SC
  { 1402,	4,	1,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo250,0,nullptr },  // Inst #1402 = SCD
  { 1403,	4,	1,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo250,0,nullptr },  // Inst #1403 = SCD_R6
  { 1404,	4,	1,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo251,0,nullptr },  // Inst #1404 = SC_MM
  { 1405,	4,	1,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo249,0,nullptr },  // Inst #1405 = SC_R6
  { 1406,	3,	0,	118,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1406 = SD
  { 1407,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1407 = SDBBP
  { 1408,	1,	0,	0,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1408 = SDBBP16_MM
  { 1409,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1409 = SDBBP_MM
  { 1410,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1410 = SDBBP_R6
  { 1411,	3,	0,	119,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo158,0,nullptr },  // Inst #1411 = SDC1
  { 1412,	3,	0,	119,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo159,0,nullptr },  // Inst #1412 = SDC164
  { 1413,	3,	0,	119,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo158,0,nullptr },  // Inst #1413 = SDC1_MM
  { 1414,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #1414 = SDC2
  { 1415,	3,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #1415 = SDC2_R6
  { 1416,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo161,0,nullptr },  // Inst #1416 = SDC3
  { 1417,	2,	0,	110,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1417 = SDIV
  { 1418,	2,	0,	110,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1418 = SDIV_MM
  { 1419,	3,	0,	120,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1419 = SDL
  { 1420,	3,	0,	121,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1420 = SDR
  { 1421,	3,	0,	122,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo168,0,nullptr },  // Inst #1421 = SDXC1
  { 1422,	3,	0,	122,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo169,0,nullptr },  // Inst #1422 = SDXC164
  { 1423,	2,	1,	123,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1423 = SEB
  { 1424,	2,	1,	123,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #1424 = SEB64
  { 1425,	2,	1,	123,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1425 = SEB_MM
  { 1426,	2,	1,	124,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1426 = SEH
  { 1427,	2,	1,	124,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #1427 = SEH64
  { 1428,	2,	1,	124,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1428 = SEH_MM
  { 1429,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1429 = SELEQZ
  { 1430,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1430 = SELEQZ64
  { 1431,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #1431 = SELEQZ_D
  { 1432,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #1432 = SELEQZ_S
  { 1433,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1433 = SELNEZ
  { 1434,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1434 = SELNEZ64
  { 1435,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo118,0,nullptr },  // Inst #1435 = SELNEZ_D
  { 1436,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo119,0,nullptr },  // Inst #1436 = SELNEZ_S
  { 1437,	4,	1,	0,	4,	0|(1<<MCID::UsesCustomInserter), 0x6ULL, nullptr, nullptr, OperandInfo252,0,nullptr },  // Inst #1437 = SEL_D
  { 1438,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo253,0,nullptr },  // Inst #1438 = SEL_S
  { 1439,	3,	1,	125,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1439 = SEQ
  { 1440,	3,	1,	126,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #1440 = SEQi
  { 1441,	3,	0,	127,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1441 = SH
  { 1442,	3,	0,	127,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo248,0,nullptr },  // Inst #1442 = SH16_MM
  { 1443,	3,	0,	127,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1443 = SH64
  { 1444,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1444 = SHF_B
  { 1445,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1445 = SHF_H
  { 1446,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1446 = SHF_W
  { 1447,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo254,0,nullptr },  // Inst #1447 = SHILO
  { 1448,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo220,0,nullptr },  // Inst #1448 = SHILOV
  { 1449,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo255,0,nullptr },  // Inst #1449 = SHLLV_PH
  { 1450,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo255,0,nullptr },  // Inst #1450 = SHLLV_QB
  { 1451,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo255,0,nullptr },  // Inst #1451 = SHLLV_S_PH
  { 1452,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo14,0,nullptr },  // Inst #1452 = SHLLV_S_W
  { 1453,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo256,0,nullptr },  // Inst #1453 = SHLL_PH
  { 1454,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo256,0,nullptr },  // Inst #1454 = SHLL_QB
  { 1455,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo256,0,nullptr },  // Inst #1455 = SHLL_S_PH
  { 1456,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList32, OperandInfo29,0,nullptr },  // Inst #1456 = SHLL_S_W
  { 1457,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo255,0,nullptr },  // Inst #1457 = SHRAV_PH
  { 1458,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo255,0,nullptr },  // Inst #1458 = SHRAV_QB
  { 1459,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo255,0,nullptr },  // Inst #1459 = SHRAV_R_PH
  { 1460,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo255,0,nullptr },  // Inst #1460 = SHRAV_R_QB
  { 1461,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1461 = SHRAV_R_W
  { 1462,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo256,0,nullptr },  // Inst #1462 = SHRA_PH
  { 1463,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo256,0,nullptr },  // Inst #1463 = SHRA_QB
  { 1464,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo256,0,nullptr },  // Inst #1464 = SHRA_R_PH
  { 1465,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo256,0,nullptr },  // Inst #1465 = SHRA_R_QB
  { 1466,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1466 = SHRA_R_W
  { 1467,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo255,0,nullptr },  // Inst #1467 = SHRLV_PH
  { 1468,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo255,0,nullptr },  // Inst #1468 = SHRLV_QB
  { 1469,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo256,0,nullptr },  // Inst #1469 = SHRL_PH
  { 1470,	3,	1,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo256,0,nullptr },  // Inst #1470 = SHRL_QB
  { 1471,	3,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1471 = SH_MM
  { 1472,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo53,0,nullptr },  // Inst #1472 = SLDI_B
  { 1473,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo54,0,nullptr },  // Inst #1473 = SLDI_D
  { 1474,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo55,0,nullptr },  // Inst #1474 = SLDI_H
  { 1475,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo56,0,nullptr },  // Inst #1475 = SLDI_W
  { 1476,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo257,0,nullptr },  // Inst #1476 = SLD_B
  { 1477,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo258,0,nullptr },  // Inst #1477 = SLD_D
  { 1478,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo259,0,nullptr },  // Inst #1478 = SLD_H
  { 1479,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo260,0,nullptr },  // Inst #1479 = SLD_W
  { 1480,	3,	1,	128,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1480 = SLL
  { 1481,	3,	1,	128,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #1481 = SLL16_MM
  { 1482,	2,	1,	128,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo109,0,nullptr },  // Inst #1482 = SLL64_32
  { 1483,	2,	1,	128,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo97,0,nullptr },  // Inst #1483 = SLL64_64
  { 1484,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1484 = SLLI_B
  { 1485,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1485 = SLLI_D
  { 1486,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1486 = SLLI_H
  { 1487,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1487 = SLLI_W
  { 1488,	3,	1,	129,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1488 = SLLV
  { 1489,	3,	1,	129,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1489 = SLLV_MM
  { 1490,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1490 = SLL_B
  { 1491,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1491 = SLL_D
  { 1492,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1492 = SLL_H
  { 1493,	3,	1,	128,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1493 = SLL_MM
  { 1494,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1494 = SLL_W
  { 1495,	3,	1,	130,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1495 = SLT
  { 1496,	3,	1,	130,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo261,0,nullptr },  // Inst #1496 = SLT64
  { 1497,	3,	1,	130,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1497 = SLT_MM
  { 1498,	3,	1,	131,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1498 = SLTi
  { 1499,	3,	1,	131,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo262,0,nullptr },  // Inst #1499 = SLTi64
  { 1500,	3,	1,	131,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1500 = SLTi_MM
  { 1501,	3,	1,	131,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1501 = SLTiu
  { 1502,	3,	1,	131,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo262,0,nullptr },  // Inst #1502 = SLTiu64
  { 1503,	3,	1,	131,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1503 = SLTiu_MM
  { 1504,	3,	1,	130,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1504 = SLTu
  { 1505,	3,	1,	130,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo261,0,nullptr },  // Inst #1505 = SLTu64
  { 1506,	3,	1,	130,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1506 = SLTu_MM
  { 1507,	3,	1,	125,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1507 = SNE
  { 1508,	3,	1,	126,	4,	0, 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #1508 = SNEi
  { 1509,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo263,0,nullptr },  // Inst #1509 = SNZ_B_PSEUDO
  { 1510,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo264,0,nullptr },  // Inst #1510 = SNZ_D_PSEUDO
  { 1511,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo265,0,nullptr },  // Inst #1511 = SNZ_H_PSEUDO
  { 1512,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo263,0,nullptr },  // Inst #1512 = SNZ_V_PSEUDO
  { 1513,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo266,0,nullptr },  // Inst #1513 = SNZ_W_PSEUDO
  { 1514,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1514 = SPLATI_B
  { 1515,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1515 = SPLATI_D
  { 1516,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1516 = SPLATI_H
  { 1517,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1517 = SPLATI_W
  { 1518,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo267,0,nullptr },  // Inst #1518 = SPLAT_B
  { 1519,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo268,0,nullptr },  // Inst #1519 = SPLAT_D
  { 1520,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo269,0,nullptr },  // Inst #1520 = SPLAT_H
  { 1521,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo270,0,nullptr },  // Inst #1521 = SPLAT_W
  { 1522,	3,	1,	132,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1522 = SRA
  { 1523,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1523 = SRAI_B
  { 1524,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1524 = SRAI_D
  { 1525,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1525 = SRAI_H
  { 1526,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1526 = SRAI_W
  { 1527,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1527 = SRARI_B
  { 1528,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1528 = SRARI_D
  { 1529,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1529 = SRARI_H
  { 1530,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1530 = SRARI_W
  { 1531,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1531 = SRAR_B
  { 1532,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1532 = SRAR_D
  { 1533,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1533 = SRAR_H
  { 1534,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1534 = SRAR_W
  { 1535,	3,	1,	133,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1535 = SRAV
  { 1536,	3,	1,	133,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1536 = SRAV_MM
  { 1537,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1537 = SRA_B
  { 1538,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1538 = SRA_D
  { 1539,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1539 = SRA_H
  { 1540,	3,	1,	132,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1540 = SRA_MM
  { 1541,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1541 = SRA_W
  { 1542,	3,	1,	134,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1542 = SRL
  { 1543,	3,	1,	134,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo17,0,nullptr },  // Inst #1543 = SRL16_MM
  { 1544,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1544 = SRLI_B
  { 1545,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1545 = SRLI_D
  { 1546,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1546 = SRLI_H
  { 1547,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1547 = SRLI_W
  { 1548,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1548 = SRLRI_B
  { 1549,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1549 = SRLRI_D
  { 1550,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1550 = SRLRI_H
  { 1551,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1551 = SRLRI_W
  { 1552,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1552 = SRLR_B
  { 1553,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1553 = SRLR_D
  { 1554,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1554 = SRLR_H
  { 1555,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1555 = SRLR_W
  { 1556,	3,	1,	135,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1556 = SRLV
  { 1557,	3,	1,	135,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1557 = SRLV_MM
  { 1558,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1558 = SRL_B
  { 1559,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1559 = SRL_D
  { 1560,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1560 = SRL_H
  { 1561,	3,	1,	134,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1561 = SRL_MM
  { 1562,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1562 = SRL_W
  { 1563,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1563 = SSNOP
  { 1564,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1564 = SSNOP_MM
  { 1565,	3,	0,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo175,0,nullptr },  // Inst #1565 = STORE_ACC128
  { 1566,	3,	0,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo176,0,nullptr },  // Inst #1566 = STORE_ACC64
  { 1567,	3,	0,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo177,0,nullptr },  // Inst #1567 = STORE_ACC64DSP
  { 1568,	3,	0,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo178,0,nullptr },  // Inst #1568 = STORE_CCOND_DSP
  { 1569,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x6ULL, nullptr, nullptr, OperandInfo170,0,nullptr },  // Inst #1569 = ST_B
  { 1570,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x6ULL, nullptr, nullptr, OperandInfo171,0,nullptr },  // Inst #1570 = ST_D
  { 1571,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x6ULL, nullptr, nullptr, OperandInfo172,0,nullptr },  // Inst #1571 = ST_H
  { 1572,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x6ULL, nullptr, nullptr, OperandInfo173,0,nullptr },  // Inst #1572 = ST_W
  { 1573,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1573 = SUB
  { 1574,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1574 = SUBQH_PH
  { 1575,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1575 = SUBQH_R_PH
  { 1576,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1576 = SUBQH_R_W
  { 1577,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1577 = SUBQH_W
  { 1578,	3,	1,	0,	4,	0, 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #1578 = SUBQ_PH
  { 1579,	3,	1,	0,	4,	0, 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #1579 = SUBQ_S_PH
  { 1580,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo14,0,nullptr },  // Inst #1580 = SUBQ_S_W
  { 1581,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1581 = SUBSUS_U_B
  { 1582,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1582 = SUBSUS_U_D
  { 1583,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1583 = SUBSUS_U_H
  { 1584,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1584 = SUBSUS_U_W
  { 1585,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1585 = SUBSUU_S_B
  { 1586,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1586 = SUBSUU_S_D
  { 1587,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1587 = SUBSUU_S_H
  { 1588,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1588 = SUBSUU_S_W
  { 1589,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1589 = SUBS_S_B
  { 1590,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1590 = SUBS_S_D
  { 1591,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1591 = SUBS_S_H
  { 1592,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1592 = SUBS_S_W
  { 1593,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1593 = SUBS_U_B
  { 1594,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1594 = SUBS_U_D
  { 1595,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1595 = SUBS_U_H
  { 1596,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1596 = SUBS_U_W
  { 1597,	3,	1,	136,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo24,0,nullptr },  // Inst #1597 = SUBU16_MM
  { 1598,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1598 = SUBUH_QB
  { 1599,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo19,0,nullptr },  // Inst #1599 = SUBUH_R_QB
  { 1600,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #1600 = SUBU_PH
  { 1601,	3,	1,	0,	4,	0, 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #1601 = SUBU_QB
  { 1602,	3,	1,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #1602 = SUBU_S_PH
  { 1603,	3,	1,	0,	4,	0, 0x6ULL, nullptr, ImplicitList1, OperandInfo19,0,nullptr },  // Inst #1603 = SUBU_S_QB
  { 1604,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1604 = SUBVI_B
  { 1605,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo26,0,nullptr },  // Inst #1605 = SUBVI_D
  { 1606,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo27,0,nullptr },  // Inst #1606 = SUBVI_H
  { 1607,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo28,0,nullptr },  // Inst #1607 = SUBVI_W
  { 1608,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1608 = SUBV_B
  { 1609,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1609 = SUBV_D
  { 1610,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1610 = SUBV_H
  { 1611,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1611 = SUBV_W
  { 1612,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1612 = SUB_MM
  { 1613,	3,	1,	136,	4,	0|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1613 = SUBu
  { 1614,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1614 = SUBu_MM
  { 1615,	3,	0,	137,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo168,0,nullptr },  // Inst #1615 = SUXC1
  { 1616,	3,	0,	137,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo169,0,nullptr },  // Inst #1616 = SUXC164
  { 1617,	3,	0,	137,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo168,0,nullptr },  // Inst #1617 = SUXC1_MM
  { 1618,	3,	0,	138,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1618 = SW
  { 1619,	3,	0,	138,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo248,0,nullptr },  // Inst #1619 = SW16_MM
  { 1620,	3,	0,	138,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1620 = SW64
  { 1621,	3,	0,	139,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo182,0,nullptr },  // Inst #1621 = SWC1
  { 1622,	3,	0,	139,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo182,0,nullptr },  // Inst #1622 = SWC1_MM
  { 1623,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #1623 = SWC2
  { 1624,	3,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo160,0,nullptr },  // Inst #1624 = SWC2_R6
  { 1625,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo161,0,nullptr },  // Inst #1625 = SWC3
  { 1626,	3,	0,	140,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1626 = SWL
  { 1627,	3,	0,	140,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1627 = SWL64
  { 1628,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo174,0,nullptr },  // Inst #1628 = SWL_MM
  { 1629,	3,	0,	0,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo185,0,nullptr },  // Inst #1629 = SWM16_MM
  { 1630,	3,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo185,0,nullptr },  // Inst #1630 = SWM32_MM
  { 1631,	4,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo186,0,nullptr },  // Inst #1631 = SWP_MM
  { 1632,	3,	0,	141,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1632 = SWR
  { 1633,	3,	0,	141,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo155,0,nullptr },  // Inst #1633 = SWR64
  { 1634,	3,	0,	0,	4,	0|(1<<MCID::MayStore), 0x2ULL, nullptr, nullptr, OperandInfo174,0,nullptr },  // Inst #1634 = SWR_MM
  { 1635,	3,	0,	138,	2,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo174,0,nullptr },  // Inst #1635 = SWSP_MM
  { 1636,	3,	0,	142,	4,	0|(1<<MCID::MayStore), 0x5ULL, nullptr, nullptr, OperandInfo187,0,nullptr },  // Inst #1636 = SWXC1
  { 1637,	3,	0,	142,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x5ULL, nullptr, nullptr, OperandInfo187,0,nullptr },  // Inst #1637 = SWXC1_MM
  { 1638,	3,	0,	0,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo154,0,nullptr },  // Inst #1638 = SW_MM
  { 1639,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #1639 = SYNC
  { 1640,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo271,0,nullptr },  // Inst #1640 = SYNCI
  { 1641,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo2,0,nullptr },  // Inst #1641 = SYNC_MM
  { 1642,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1642 = SYSCALL
  { 1643,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1643 = SYSCALL_MM
  { 1644,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo263,0,nullptr },  // Inst #1644 = SZ_B_PSEUDO
  { 1645,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo264,0,nullptr },  // Inst #1645 = SZ_D_PSEUDO
  { 1646,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo265,0,nullptr },  // Inst #1646 = SZ_H_PSEUDO
  { 1647,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo263,0,nullptr },  // Inst #1647 = SZ_V_PSEUDO
  { 1648,	2,	1,	3,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo266,0,nullptr },  // Inst #1648 = SZ_W_PSEUDO
  { 1649,	0,	0,	143,	2,	0|(1<<MCID::MayStore)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, nullptr,0,nullptr },  // Inst #1649 = Save16
  { 1650,	0,	0,	143,	2,	0|(1<<MCID::MayStore)|(1<<MCID::Variadic)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, ImplicitList3, ImplicitList3, nullptr,0,nullptr },  // Inst #1650 = SaveX16
  { 1651,	4,	0,	117,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #1651 = SbRxRyOffMemX16
  { 1652,	2,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo272,0,nullptr },  // Inst #1652 = SebRx16
  { 1653,	2,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo272,0,nullptr },  // Inst #1653 = SehRx16
  { 1654,	4,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo273,0,nullptr },  // Inst #1654 = SelBeqZ
  { 1655,	4,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo273,0,nullptr },  // Inst #1655 = SelBneZ
  { 1656,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo274,0,nullptr },  // Inst #1656 = SelTBteqZCmp
  { 1657,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo275,0,nullptr },  // Inst #1657 = SelTBteqZCmpi
  { 1658,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo274,0,nullptr },  // Inst #1658 = SelTBteqZSlt
  { 1659,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo275,0,nullptr },  // Inst #1659 = SelTBteqZSlti
  { 1660,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo275,0,nullptr },  // Inst #1660 = SelTBteqZSltiu
  { 1661,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo274,0,nullptr },  // Inst #1661 = SelTBteqZSltu
  { 1662,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo274,0,nullptr },  // Inst #1662 = SelTBtneZCmp
  { 1663,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo275,0,nullptr },  // Inst #1663 = SelTBtneZCmpi
  { 1664,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo274,0,nullptr },  // Inst #1664 = SelTBtneZSlt
  { 1665,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo275,0,nullptr },  // Inst #1665 = SelTBtneZSlti
  { 1666,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo275,0,nullptr },  // Inst #1666 = SelTBtneZSltiu
  { 1667,	5,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo274,0,nullptr },  // Inst #1667 = SelTBtneZSltu
  { 1668,	4,	0,	127,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #1668 = ShRxRyOffMemX16
  { 1669,	3,	1,	6,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo276,0,nullptr },  // Inst #1669 = SllX16
  { 1670,	3,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo43,0,nullptr },  // Inst #1670 = SllvRxRy16
  { 1671,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo42,0,nullptr },  // Inst #1671 = SltCCRxRy16
  { 1672,	2,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo94,0,nullptr },  // Inst #1672 = SltRxRy16
  { 1673,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo276,0,nullptr },  // Inst #1673 = SltiCCRxImmX16
  { 1674,	2,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo39,0,nullptr },  // Inst #1674 = SltiRxImm16
  { 1675,	2,	0,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo39,0,nullptr },  // Inst #1675 = SltiRxImmX16
  { 1676,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo276,0,nullptr },  // Inst #1676 = SltiuCCRxImmX16
  { 1677,	2,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo39,0,nullptr },  // Inst #1677 = SltiuRxImm16
  { 1678,	2,	0,	6,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo39,0,nullptr },  // Inst #1678 = SltiuRxImmX16
  { 1679,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UsesCustomInserter), 0x0ULL, nullptr, nullptr, OperandInfo42,0,nullptr },  // Inst #1679 = SltuCCRxRy16
  { 1680,	2,	0,	6,	2,	0|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo94,0,nullptr },  // Inst #1680 = SltuRxRy16
  { 1681,	3,	1,	3,	2,	0|(1<<MCID::Pseudo)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, ImplicitList7, OperandInfo42,0,nullptr },  // Inst #1681 = SltuRxRyRz16
  { 1682,	3,	1,	6,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo276,0,nullptr },  // Inst #1682 = SraX16
  { 1683,	3,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo43,0,nullptr },  // Inst #1683 = SravRxRy16
  { 1684,	3,	1,	6,	4,	0, 0x0ULL, nullptr, nullptr, OperandInfo276,0,nullptr },  // Inst #1684 = SrlX16
  { 1685,	3,	1,	6,	2,	0, 0x0ULL, nullptr, nullptr, OperandInfo43,0,nullptr },  // Inst #1685 = SrlvRxRy16
  { 1686,	3,	1,	6,	2,	0|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo42,0,nullptr },  // Inst #1686 = SubuRxRyRz16
  { 1687,	4,	0,	138,	4,	0|(1<<MCID::MayStore), 0x0ULL, nullptr, nullptr, OperandInfo188,0,nullptr },  // Inst #1687 = SwRxRyOffMemX16
  { 1688,	3,	0,	138,	4,	0|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, OperandInfo191,0,nullptr },  // Inst #1688 = SwRxSpImmX16
  { 1689,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::Terminator)|(1<<MCID::ExtraSrcRegAllocReq), 0x0ULL, nullptr, ImplicitList4, OperandInfo5,0,nullptr },  // Inst #1689 = TAILCALL
  { 1690,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::Terminator)|(1<<MCID::ExtraSrcRegAllocReq), 0x0ULL, nullptr, ImplicitList4, OperandInfo152,0,nullptr },  // Inst #1690 = TAILCALL64_R
  { 1691,	1,	0,	7,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Return)|(1<<MCID::Barrier)|(1<<MCID::DelaySlot)|(1<<MCID::Call)|(1<<MCID::Terminator)|(1<<MCID::ExtraSrcRegAllocReq), 0x0ULL, nullptr, ImplicitList4, OperandInfo65,0,nullptr },  // Inst #1691 = TAILCALL_R
  { 1692,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1692 = TEQ
  { 1693,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1693 = TEQI
  { 1694,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1694 = TEQI_MM
  { 1695,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1695 = TEQ_MM
  { 1696,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1696 = TGE
  { 1697,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1697 = TGEI
  { 1698,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1698 = TGEIU
  { 1699,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1699 = TGEIU_MM
  { 1700,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1700 = TGEI_MM
  { 1701,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1701 = TGEU
  { 1702,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1702 = TGEU_MM
  { 1703,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1703 = TGE_MM
  { 1704,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1704 = TLBP
  { 1705,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1705 = TLBP_MM
  { 1706,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1706 = TLBR
  { 1707,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1707 = TLBR_MM
  { 1708,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1708 = TLBWI
  { 1709,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1709 = TLBWI_MM
  { 1710,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1710 = TLBWR
  { 1711,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1711 = TLBWR_MM
  { 1712,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1712 = TLT
  { 1713,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1713 = TLTI
  { 1714,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1714 = TLTIU_MM
  { 1715,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1715 = TLTI_MM
  { 1716,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1716 = TLTU
  { 1717,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1717 = TLTU_MM
  { 1718,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1718 = TLT_MM
  { 1719,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1719 = TNE
  { 1720,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1720 = TNEI
  { 1721,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1721 = TNEI_MM
  { 1722,	3,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1722 = TNE_MM
  { 1723,	0,	0,	0,	4,	0|(1<<MCID::Pseudo)|(1<<MCID::Barrier)|(1<<MCID::Terminator)|(1<<MCID::UnmodeledSideEffects), 0x0ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1723 = TRAP
  { 1724,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo73,0,nullptr },  // Inst #1724 = TRUNC_L_D64
  { 1725,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo74,0,nullptr },  // Inst #1725 = TRUNC_L_S
  { 1726,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #1726 = TRUNC_W_D32
  { 1727,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo76,0,nullptr },  // Inst #1727 = TRUNC_W_D64
  { 1728,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo75,0,nullptr },  // Inst #1728 = TRUNC_W_MM
  { 1729,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #1729 = TRUNC_W_S
  { 1730,	2,	1,	144,	4,	0, 0x4ULL, nullptr, nullptr, OperandInfo77,0,nullptr },  // Inst #1730 = TRUNC_W_S_MM
  { 1731,	2,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1731 = TTLTIU
  { 1732,	2,	0,	111,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1732 = UDIV
  { 1733,	2,	0,	111,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList12, OperandInfo13,0,nullptr },  // Inst #1733 = UDIV_MM
  { 1734,	3,	1,	22,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList33, OperandInfo32,0,nullptr },  // Inst #1734 = V3MULU
  { 1735,	3,	1,	22,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList25, OperandInfo32,0,nullptr },  // Inst #1735 = VMM0
  { 1736,	3,	1,	22,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, ImplicitList34, OperandInfo32,0,nullptr },  // Inst #1736 = VMULU
  { 1737,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo57,0,nullptr },  // Inst #1737 = VSHF_B
  { 1738,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo58,0,nullptr },  // Inst #1738 = VSHF_D
  { 1739,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo59,0,nullptr },  // Inst #1739 = VSHF_H
  { 1740,	4,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo60,0,nullptr },  // Inst #1740 = VSHF_W
  { 1741,	0,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, nullptr,0,nullptr },  // Inst #1741 = WAIT
  { 1742,	1,	0,	0,	4,	0|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo5,0,nullptr },  // Inst #1742 = WAIT_MM
  { 1743,	2,	0,	0,	4,	0|(1<<MCID::MayLoad)|(1<<MCID::MayStore)|(1<<MCID::UnmodeledSideEffects), 0x6ULL, nullptr, nullptr, OperandInfo15,0,nullptr },  // Inst #1743 = WRDSP
  { 1744,	2,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1744 = WSBH
  { 1745,	2,	1,	0,	4,	0, 0x1ULL, nullptr, nullptr, OperandInfo13,0,nullptr },  // Inst #1745 = WSBH_MM
  { 1746,	3,	1,	145,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1746 = XOR
  { 1747,	3,	1,	145,	2,	0|(1<<MCID::Commutable), 0x0ULL, nullptr, nullptr, OperandInfo31,0,nullptr },  // Inst #1747 = XOR16_MM
  { 1748,	3,	1,	145,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x1ULL, nullptr, nullptr, OperandInfo32,0,nullptr },  // Inst #1748 = XOR64
  { 1749,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo25,0,nullptr },  // Inst #1749 = XORI_B
  { 1750,	3,	1,	145,	4,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x1ULL, nullptr, nullptr, OperandInfo14,0,nullptr },  // Inst #1750 = XOR_MM
  { 1751,	3,	1,	0,	4,	0, 0x6ULL, nullptr, nullptr, OperandInfo20,0,nullptr },  // Inst #1751 = XOR_V
  { 1752,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo21,0,nullptr },  // Inst #1752 = XOR_V_D_PSEUDO
  { 1753,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo22,0,nullptr },  // Inst #1753 = XOR_V_H_PSEUDO
  { 1754,	3,	1,	3,	4,	0|(1<<MCID::Pseudo), 0x0ULL, nullptr, nullptr, OperandInfo23,0,nullptr },  // Inst #1754 = XOR_V_W_PSEUDO
  { 1755,	3,	1,	146,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1755 = XORi
  { 1756,	3,	1,	145,	4,	0|(1<<MCID::Rematerializable), 0x2ULL, nullptr, nullptr, OperandInfo33,0,nullptr },  // Inst #1756 = XORi64
  { 1757,	3,	1,	0,	4,	0|(1<<MCID::Rematerializable)|(1<<MCID::UnmodeledSideEffects), 0x2ULL, nullptr, nullptr, OperandInfo29,0,nullptr },  // Inst #1757 = XORi_MM
  { 1758,	3,	1,	6,	2,	0|(1<<MCID::Commutable)|(1<<MCID::Rematerializable), 0x0ULL, nullptr, nullptr, OperandInfo43,0,nullptr },  // Inst #1758 = XorRxRxRy16
};

extern const char MipsInstrNameData[] = {
  /* 0 */ 'D', 'M', 'F', 'C', '0', 0,
  /* 6 */ 'D', 'M', 'T', 'C', '0', 0,
  /* 12 */ 'V', 'M', 'M', '0', 0,
  /* 17 */ 'M', 'T', 'M', '0', 0,
  /* 22 */ 'M', 'T', 'P', '0', 0,
  /* 27 */ 'L', 'D', 'C', '1', 0,
  /* 32 */ 'S', 'D', 'C', '1', 0,
  /* 37 */ 'C', 'F', 'C', '1', 0,
  /* 42 */ 'D', 'M', 'F', 'C', '1', 0,
  /* 48 */ 'C', 'T', 'C', '1', 0,
  /* 53 */ 'D', 'M', 'T', 'C', '1', 0,
  /* 59 */ 'L', 'W', 'C', '1', 0,
  /* 64 */ 'S', 'W', 'C', '1', 0,
  /* 69 */ 'L', 'D', 'X', 'C', '1', 0,
  /* 75 */ 'S', 'D', 'X', 'C', '1', 0,
  /* 81 */ 'L', 'U', 'X', 'C', '1', 0,
  /* 87 */ 'S', 'U', 'X', 'C', '1', 0,
  /* 93 */ 'L', 'W', 'X', 'C', '1', 0,
  /* 99 */ 'S', 'W', 'X', 'C', '1', 0,
  /* 105 */ 'M', 'T', 'M', '1', 0,
  /* 110 */ 'M', 'T', 'P', '1', 0,
  /* 115 */ 'D', 'S', 'R', 'A', '3', '2', 0,
  /* 122 */ 'M', 'F', 'H', 'C', '1', '_', 'D', '3', '2', 0,
  /* 132 */ 'M', 'T', 'H', 'C', '1', '_', 'D', '3', '2', 0,
  /* 142 */ 'F', 'S', 'U', 'B', '_', 'D', '3', '2', 0,
  /* 151 */ 'N', 'M', 'S', 'U', 'B', '_', 'D', '3', '2', 0,
  /* 161 */ 'F', 'A', 'D', 'D', '_', 'D', '3', '2', 0,
  /* 170 */ 'N', 'M', 'A', 'D', 'D', '_', 'D', '3', '2', 0,
  /* 180 */ 'C', '_', 'N', 'G', 'E', '_', 'D', '3', '2', 0,
  /* 190 */ 'C', '_', 'N', 'G', 'L', 'E', '_', 'D', '3', '2', 0,
  /* 201 */ 'C', '_', 'O', 'L', 'E', '_', 'D', '3', '2', 0,
  /* 211 */ 'C', '_', 'U', 'L', 'E', '_', 'D', '3', '2', 0,
  /* 221 */ 'C', '_', 'L', 'E', '_', 'D', '3', '2', 0,
  /* 230 */ 'C', '_', 'S', 'F', '_', 'D', '3', '2', 0,
  /* 239 */ 'M', 'O', 'V', 'F', '_', 'D', '3', '2', 0,
  /* 248 */ 'C', '_', 'F', '_', 'D', '3', '2', 0,
  /* 256 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'F', '_', 'D', '3', '2', 0,
  /* 277 */ 'F', 'N', 'E', 'G', '_', 'D', '3', '2', 0,
  /* 286 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'D', '3', '2', 0,
  /* 297 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'D', '3', '2', 0,
  /* 308 */ 'C', '_', 'N', 'G', 'L', '_', 'D', '3', '2', 0,
  /* 318 */ 'F', 'M', 'U', 'L', '_', 'D', '3', '2', 0,
  /* 327 */ 'C', '_', 'U', 'N', '_', 'D', '3', '2', 0,
  /* 336 */ 'F', 'C', 'M', 'P', '_', 'D', '3', '2', 0,
  /* 345 */ 'C', '_', 'S', 'E', 'Q', '_', 'D', '3', '2', 0,
  /* 355 */ 'C', '_', 'U', 'E', 'Q', '_', 'D', '3', '2', 0,
  /* 365 */ 'C', '_', 'E', 'Q', '_', 'D', '3', '2', 0,
  /* 374 */ 'F', 'A', 'B', 'S', '_', 'D', '3', '2', 0,
  /* 383 */ 'C', 'V', 'T', '_', 'S', '_', 'D', '3', '2', 0,
  /* 393 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', '_', 'D', '3', '2', 0,
  /* 410 */ 'C', '_', 'N', 'G', 'T', '_', 'D', '3', '2', 0,
  /* 420 */ 'C', '_', 'O', 'L', 'T', '_', 'D', '3', '2', 0,
  /* 430 */ 'C', '_', 'U', 'L', 'T', '_', 'D', '3', '2', 0,
  /* 440 */ 'C', '_', 'L', 'T', '_', 'D', '3', '2', 0,
  /* 449 */ 'F', 'S', 'Q', 'R', 'T', '_', 'D', '3', '2', 0,
  /* 459 */ 'M', 'O', 'V', 'T', '_', 'D', '3', '2', 0,
  /* 468 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'T', '_', 'D', '3', '2', 0,
  /* 489 */ 'F', 'D', 'I', 'V', '_', 'D', '3', '2', 0,
  /* 498 */ 'F', 'M', 'O', 'V', '_', 'D', '3', '2', 0,
  /* 507 */ 'T', 'R', 'U', 'N', 'C', '_', 'W', '_', 'D', '3', '2', 0,
  /* 519 */ 'R', 'O', 'U', 'N', 'D', '_', 'W', '_', 'D', '3', '2', 0,
  /* 531 */ 'C', 'E', 'I', 'L', '_', 'W', '_', 'D', '3', '2', 0,
  /* 542 */ 'F', 'L', 'O', 'O', 'R', '_', 'W', '_', 'D', '3', '2', 0,
  /* 554 */ 'C', 'V', 'T', '_', 'W', '_', 'D', '3', '2', 0,
  /* 564 */ 'B', 'P', 'O', 'S', 'G', 'E', '3', '2', 0,
  /* 573 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'S', 'U', 'B', '_', 'I', '3', '2', 0,
  /* 593 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'D', 'D', '_', 'I', '3', '2', 0,
  /* 613 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'N', 'A', 'N', 'D', '_', 'I', '3', '2', 0,
  /* 634 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'N', 'D', '_', 'I', '3', '2', 0,
  /* 654 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'S', 'W', 'A', 'P', '_', 'I', '3', '2', 0,
  /* 670 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'C', 'M', 'P', '_', 'S', 'W', 'A', 'P', '_', 'I', '3', '2', 0,
  /* 690 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'X', 'O', 'R', '_', 'I', '3', '2', 0,
  /* 710 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'O', 'R', '_', 'I', '3', '2', 0,
  /* 729 */ 'D', 'S', 'L', 'L', '3', '2', 0,
  /* 736 */ 'D', 'S', 'R', 'L', '3', '2', 0,
  /* 743 */ 'D', 'R', 'O', 'T', 'R', '3', '2', 0,
  /* 751 */ 'C', 'I', 'N', 'S', '3', '2', 0,
  /* 758 */ 'E', 'X', 'T', 'S', '3', '2', 0,
  /* 765 */ 'F', 'C', 'M', 'P', '_', 'S', '3', '2', 0,
  /* 774 */ 'D', 'S', 'L', 'L', '6', '4', '_', '3', '2', 0,
  /* 784 */ 'M', 'I', 'P', 'S', 'e', 'h', '_', 'r', 'e', 't', 'u', 'r', 'n', '3', '2', 0,
  /* 800 */ 'L', 'w', 'C', 'o', 'n', 's', 't', 'a', 'n', 't', '3', '2', 0,
  /* 813 */ 'L', 'D', 'C', '2', 0,
  /* 818 */ 'S', 'D', 'C', '2', 0,
  /* 823 */ 'D', 'M', 'F', 'C', '2', 0,
  /* 829 */ 'D', 'M', 'T', 'C', '2', 0,
  /* 835 */ 'L', 'W', 'C', '2', 0,
  /* 840 */ 'S', 'W', 'C', '2', 0,
  /* 845 */ 'M', 'T', 'M', '2', 0,
  /* 850 */ 'M', 'T', 'P', '2', 0,
  /* 855 */ 'L', 'D', 'C', '3', 0,
  /* 860 */ 'S', 'D', 'C', '3', 0,
  /* 865 */ 'L', 'W', 'C', '3', 0,
  /* 870 */ 'S', 'W', 'C', '3', 0,
  /* 875 */ 'L', 'D', 'C', '1', '6', '4', 0,
  /* 882 */ 'S', 'D', 'C', '1', '6', '4', 0,
  /* 889 */ 'L', 'D', 'X', 'C', '1', '6', '4', 0,
  /* 897 */ 'S', 'D', 'X', 'C', '1', '6', '4', 0,
  /* 905 */ 'L', 'U', 'X', 'C', '1', '6', '4', 0,
  /* 913 */ 'S', 'U', 'X', 'C', '1', '6', '4', 0,
  /* 921 */ 'S', 'E', 'B', '6', '4', 0,
  /* 927 */ 'L', 'B', '6', '4', 0,
  /* 932 */ 'S', 'B', '6', '4', 0,
  /* 937 */ 'L', 'O', 'A', 'D', '_', 'A', 'C', 'C', '6', '4', 0,
  /* 948 */ 'S', 'T', 'O', 'R', 'E', '_', 'A', 'C', 'C', '6', '4', 0,
  /* 960 */ 'A', 'N', 'D', '6', '4', 0,
  /* 966 */ 'M', 'F', 'H', 'C', '1', '_', 'D', '6', '4', 0,
  /* 976 */ 'M', 'T', 'H', 'C', '1', '_', 'D', '6', '4', 0,
  /* 986 */ 'M', 'O', 'V', 'N', '_', 'I', '6', '4', '_', 'D', '6', '4', 0,
  /* 999 */ 'M', 'O', 'V', 'Z', '_', 'I', '6', '4', '_', 'D', '6', '4', 0,
  /* 1012 */ 'F', 'S', 'U', 'B', '_', 'D', '6', '4', 0,
  /* 1021 */ 'N', 'M', 'S', 'U', 'B', '_', 'D', '6', '4', 0,
  /* 1031 */ 'F', 'A', 'D', 'D', '_', 'D', '6', '4', 0,
  /* 1040 */ 'N', 'M', 'A', 'D', 'D', '_', 'D', '6', '4', 0,
  /* 1050 */ 'C', '_', 'N', 'G', 'E', '_', 'D', '6', '4', 0,
  /* 1060 */ 'C', '_', 'N', 'G', 'L', 'E', '_', 'D', '6', '4', 0,
  /* 1071 */ 'C', '_', 'O', 'L', 'E', '_', 'D', '6', '4', 0,
  /* 1081 */ 'C', '_', 'U', 'L', 'E', '_', 'D', '6', '4', 0,
  /* 1091 */ 'C', '_', 'L', 'E', '_', 'D', '6', '4', 0,
  /* 1100 */ 'C', '_', 'S', 'F', '_', 'D', '6', '4', 0,
  /* 1109 */ 'M', 'O', 'V', 'F', '_', 'D', '6', '4', 0,
  /* 1118 */ 'C', '_', 'F', '_', 'D', '6', '4', 0,
  /* 1126 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'F', '_', 'D', '6', '4', 0,
  /* 1147 */ 'F', 'N', 'E', 'G', '_', 'D', '6', '4', 0,
  /* 1156 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'D', '6', '4', 0,
  /* 1167 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'D', '6', '4', 0,
  /* 1178 */ 'C', '_', 'N', 'G', 'L', '_', 'D', '6', '4', 0,
  /* 1188 */ 'F', 'M', 'U', 'L', '_', 'D', '6', '4', 0,
  /* 1197 */ 'T', 'R', 'U', 'N', 'C', '_', 'L', '_', 'D', '6', '4', 0,
  /* 1209 */ 'R', 'O', 'U', 'N', 'D', '_', 'L', '_', 'D', '6', '4', 0,
  /* 1221 */ 'C', 'E', 'I', 'L', '_', 'L', '_', 'D', '6', '4', 0,
  /* 1232 */ 'F', 'L', 'O', 'O', 'R', '_', 'L', '_', 'D', '6', '4', 0,
  /* 1244 */ 'C', 'V', 'T', '_', 'L', '_', 'D', '6', '4', 0,
  /* 1254 */ 'C', '_', 'U', 'N', '_', 'D', '6', '4', 0,
  /* 1263 */ 'F', 'C', 'M', 'P', '_', 'D', '6', '4', 0,
  /* 1272 */ 'C', '_', 'S', 'E', 'Q', '_', 'D', '6', '4', 0,
  /* 1282 */ 'C', '_', 'U', 'E', 'Q', '_', 'D', '6', '4', 0,
  /* 1292 */ 'C', '_', 'E', 'Q', '_', 'D', '6', '4', 0,
  /* 1301 */ 'F', 'A', 'B', 'S', '_', 'D', '6', '4', 0,
  /* 1310 */ 'C', 'V', 'T', '_', 'S', '_', 'D', '6', '4', 0,
  /* 1320 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', '_', 'D', '6', '4', 0,
  /* 1337 */ 'C', '_', 'N', 'G', 'T', '_', 'D', '6', '4', 0,
  /* 1347 */ 'C', '_', 'O', 'L', 'T', '_', 'D', '6', '4', 0,
  /* 1357 */ 'C', '_', 'U', 'L', 'T', '_', 'D', '6', '4', 0,
  /* 1367 */ 'C', '_', 'L', 'T', '_', 'D', '6', '4', 0,
  /* 1376 */ 'F', 'S', 'Q', 'R', 'T', '_', 'D', '6', '4', 0,
  /* 1386 */ 'M', 'O', 'V', 'T', '_', 'D', '6', '4', 0,
  /* 1395 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'T', '_', 'D', '6', '4', 0,
  /* 1416 */ 'F', 'D', 'I', 'V', '_', 'D', '6', '4', 0,
  /* 1425 */ 'F', 'M', 'O', 'V', '_', 'D', '6', '4', 0,
  /* 1434 */ 'T', 'R', 'U', 'N', 'C', '_', 'W', '_', 'D', '6', '4', 0,
  /* 1446 */ 'R', 'O', 'U', 'N', 'D', '_', 'W', '_', 'D', '6', '4', 0,
  /* 1458 */ 'C', 'E', 'I', 'L', '_', 'W', '_', 'D', '6', '4', 0,
  /* 1469 */ 'F', 'L', 'O', 'O', 'R', '_', 'W', '_', 'D', '6', '4', 0,
  /* 1481 */ 'C', 'V', 'T', '_', 'W', '_', 'D', '6', '4', 0,
  /* 1491 */ 'B', 'N', 'E', '6', '4', 0,
  /* 1497 */ 'B', 'u', 'i', 'l', 'd', 'P', 'a', 'i', 'r', 'F', '6', '4', 0,
  /* 1510 */ 'E', 'x', 't', 'r', 'a', 'c', 't', 'E', 'l', 'e', 'm', 'e', 'n', 't', 'F', '6', '4', 0,
  /* 1528 */ 'S', 'E', 'H', '6', '4', 0,
  /* 1534 */ 'L', 'H', '6', '4', 0,
  /* 1539 */ 'S', 'H', '6', '4', 0,
  /* 1544 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'F', 'H', 'I', '6', '4', 0,
  /* 1557 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'T', 'L', 'O', 'H', 'I', '6', '4', 0,
  /* 1572 */ 'M', 'T', 'H', 'I', '6', '4', 0,
  /* 1579 */ 'M', 'O', 'V', 'N', '_', 'I', '6', '4', '_', 'I', '6', '4', 0,
  /* 1592 */ 'M', 'O', 'V', 'Z', '_', 'I', '6', '4', '_', 'I', '6', '4', 0,
  /* 1605 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'S', 'U', 'B', '_', 'I', '6', '4', 0,
  /* 1625 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'D', 'D', '_', 'I', '6', '4', 0,
  /* 1645 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'N', 'A', 'N', 'D', '_', 'I', '6', '4', 0,
  /* 1666 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'N', 'D', '_', 'I', '6', '4', 0,
  /* 1686 */ 'M', 'O', 'V', 'F', '_', 'I', '6', '4', 0,
  /* 1695 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'F', '_', 'I', '6', '4', 0,
  /* 1716 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'I', '6', '4', 0,
  /* 1727 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'I', '6', '4', 0,
  /* 1738 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'S', 'W', 'A', 'P', '_', 'I', '6', '4', 0,
  /* 1754 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'C', 'M', 'P', '_', 'S', 'W', 'A', 'P', '_', 'I', '6', '4', 0,
  /* 1774 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'X', 'O', 'R', '_', 'I', '6', '4', 0,
  /* 1794 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'O', 'R', '_', 'I', '6', '4', 0,
  /* 1813 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', '_', 'I', '6', '4', 0,
  /* 1830 */ 'M', 'O', 'V', 'T', '_', 'I', '6', '4', 0,
  /* 1839 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'T', '_', 'I', '6', '4', 0,
  /* 1860 */ 'L', 'W', 'L', '6', '4', 0,
  /* 1866 */ 'S', 'W', 'L', '6', '4', 0,
  /* 1872 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'F', 'L', 'O', '6', '4', 0,
  /* 1885 */ 'M', 'T', 'L', 'O', '6', '4', 0,
  /* 1892 */ 'B', 'E', 'Q', '6', '4', 0,
  /* 1898 */ 'J', 'R', '6', '4', 0,
  /* 1903 */ 'J', 'A', 'L', 'R', '6', '4', 0,
  /* 1910 */ 'N', 'O', 'R', '6', '4', 0,
  /* 1916 */ 'X', 'O', 'R', '6', '4', 0,
  /* 1922 */ 'R', 'D', 'H', 'W', 'R', '6', '4', 0,
  /* 1930 */ 'L', 'W', 'R', '6', '4', 0,
  /* 1936 */ 'S', 'W', 'R', '6', '4', 0,
  /* 1942 */ 'S', 'L', 'T', '6', '4', 0,
  /* 1948 */ 'L', 'W', '6', '4', 0,
  /* 1953 */ 'S', 'W', '6', '4', 0,
  /* 1958 */ 'B', 'G', 'E', 'Z', '6', '4', 0,
  /* 1965 */ 'B', 'L', 'E', 'Z', '6', '4', 0,
  /* 1972 */ 'S', 'E', 'L', 'N', 'E', 'Z', '6', '4', 0,
  /* 1981 */ 'S', 'E', 'L', 'E', 'Q', 'Z', '6', '4', 0,
  /* 1990 */ 'B', 'G', 'T', 'Z', '6', '4', 0,
  /* 1997 */ 'B', 'L', 'T', 'Z', '6', '4', 0,
  /* 2004 */ 'B', 'u', 'i', 'l', 'd', 'P', 'a', 'i', 'r', 'F', '6', '4', '_', '6', '4', 0,
  /* 2020 */ 'E', 'x', 't', 'r', 'a', 'c', 't', 'E', 'l', 'e', 'm', 'e', 'n', 't', 'F', '6', '4', '_', '6', '4', 0,
  /* 2041 */ 'S', 'L', 'L', '6', '4', '_', '6', '4', 0,
  /* 2050 */ 'P', 's', 'e', 'u', 'd', 'o', 'I', 'n', 'd', 'i', 'r', 'e', 'c', 't', 'B', 'r', 'a', 'n', 'c', 'h', '6', '4', 0,
  /* 2073 */ 'A', 'N', 'D', 'i', '6', '4', 0,
  /* 2080 */ 'X', 'O', 'R', 'i', '6', '4', 0,
  /* 2087 */ 'S', 'L', 'T', 'i', '6', '4', 0,
  /* 2094 */ 'L', 'U', 'i', '6', '4', 0,
  /* 2100 */ 'P', 's', 'e', 'u', 'd', 'o', 'R', 'e', 't', 'u', 'r', 'n', '6', '4', 0,
  /* 2115 */ 'M', 'I', 'P', 'S', 'e', 'h', '_', 'r', 'e', 't', 'u', 'r', 'n', '6', '4', 0,
  /* 2131 */ 'L', 'B', 'u', '6', '4', 0,
  /* 2137 */ 'L', 'H', 'u', '6', '4', 0,
  /* 2143 */ 'S', 'L', 'T', 'u', '6', '4', 0,
  /* 2150 */ 'L', 'E', 'A', '_', 'A', 'D', 'D', 'i', 'u', '6', '4', 0,
  /* 2162 */ 'S', 'L', 'T', 'i', 'u', '6', '4', 0,
  /* 2170 */ 'M', 'o', 'v', 'e', 'R', '3', '2', '1', '6', 0,
  /* 2180 */ 'R', 'e', 't', 'R', 'A', '1', '6', 0,
  /* 2188 */ 'J', 'a', 'l', 'B', '1', '6', 0,
  /* 2195 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'S', 'U', 'B', '_', 'I', '1', '6', 0,
  /* 2215 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'D', 'D', '_', 'I', '1', '6', 0,
  /* 2235 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'N', 'A', 'N', 'D', '_', 'I', '1', '6', 0,
  /* 2256 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'N', 'D', '_', 'I', '1', '6', 0,
  /* 2276 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'S', 'W', 'A', 'P', '_', 'I', '1', '6', 0,
  /* 2292 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'C', 'M', 'P', '_', 'S', 'W', 'A', 'P', '_', 'I', '1', '6', 0,
  /* 2312 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'X', 'O', 'R', '_', 'I', '1', '6', 0,
  /* 2332 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'O', 'R', '_', 'I', '1', '6', 0,
  /* 2351 */ 'M', 'o', 'v', 'e', '3', '2', 'R', '1', '6', 0,
  /* 2361 */ 'S', 'r', 'a', 'X', '1', '6', 0,
  /* 2368 */ 'R', 'e', 's', 't', 'o', 'r', 'e', 'X', '1', '6', 0,
  /* 2379 */ 'S', 'a', 'v', 'e', 'X', '1', '6', 0,
  /* 2387 */ 'B', 't', 'n', 'e', 'z', 'T', '8', 'C', 'm', 'p', 'i', 'X', '1', '6', 0,
  /* 2402 */ 'B', 't', 'e', 'q', 'z', 'T', '8', 'C', 'm', 'p', 'i', 'X', '1', '6', 0,
  /* 2417 */ 'B', 't', 'n', 'e', 'z', 'T', '8', 'S', 'l', 't', 'i', 'X', '1', '6', 0,
  /* 2432 */ 'B', 't', 'e', 'q', 'z', 'T', '8', 'S', 'l', 't', 'i', 'X', '1', '6', 0,
  /* 2447 */ 'S', 'l', 'l', 'X', '1', '6', 0,
  /* 2454 */ 'S', 'r', 'l', 'X', '1', '6', 0,
  /* 2461 */ 'L', 'b', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2477 */ 'S', 'b', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2493 */ 'L', 'h', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2509 */ 'S', 'h', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2525 */ 'L', 'b', 'u', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2542 */ 'L', 'h', 'u', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2559 */ 'A', 'd', 'd', 'i', 'u', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2578 */ 'L', 'w', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2594 */ 'S', 'w', 'R', 'x', 'R', 'y', 'O', 'f', 'f', 'M', 'e', 'm', 'X', '1', '6', 0,
  /* 2610 */ 'A', 'd', 'd', 'i', 'u', 'R', 'x', 'P', 'c', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2626 */ 'A', 'd', 'd', 'i', 'u', 'S', 'p', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2640 */ 'L', 'w', 'R', 'x', 'S', 'p', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2653 */ 'S', 'w', 'R', 'x', 'S', 'p', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2666 */ 'S', 'l', 't', 'i', 'C', 'C', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2681 */ 'S', 'l', 't', 'i', 'u', 'C', 'C', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2697 */ 'L', 'i', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2708 */ 'C', 'm', 'p', 'i', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2721 */ 'S', 'l', 't', 'i', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2734 */ 'A', 'd', 'd', 'i', 'u', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2748 */ 'S', 'l', 't', 'i', 'u', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2762 */ 'A', 'd', 'd', 'i', 'u', 'R', 'x', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2778 */ 'B', 'n', 'e', 'z', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2791 */ 'B', 'e', 'q', 'z', 'R', 'x', 'I', 'm', 'm', 'X', '1', '6', 0,
  /* 2804 */ 'B', 'i', 'm', 'm', 'X', '1', '6', 0,
  /* 2812 */ 'L', 'i', 'R', 'x', 'I', 'm', 'm', 'A', 'l', 'i', 'g', 'n', 'X', '1', '6', 0,
  /* 2828 */ 'L', 'w', 'R', 'x', 'P', 'c', 'T', 'c', 'p', 'X', '1', '6', 0,
  /* 2841 */ 'B', 't', 'n', 'e', 'z', 'T', '8', 'C', 'm', 'p', 'X', '1', '6', 0,
  /* 2855 */ 'B', 't', 'e', 'q', 'z', 'T', '8', 'C', 'm', 'p', 'X', '1', '6', 0,
  /* 2869 */ 'B', 't', 'n', 'e', 'z', 'T', '8', 'S', 'l', 't', 'X', '1', '6', 0,
  /* 2883 */ 'B', 't', 'e', 'q', 'z', 'T', '8', 'S', 'l', 't', 'X', '1', '6', 0,
  /* 2897 */ 'B', 't', 'n', 'e', 'z', 'T', '8', 'S', 'l', 't', 'i', 'u', 'X', '1', '6', 0,
  /* 2913 */ 'B', 't', 'e', 'q', 'z', 'T', '8', 'S', 'l', 't', 'i', 'u', 'X', '1', '6', 0,
  /* 2929 */ 'B', 't', 'n', 'e', 'z', 'T', '8', 'S', 'l', 't', 'u', 'X', '1', '6', 0,
  /* 2944 */ 'B', 't', 'e', 'q', 'z', 'T', '8', 'S', 'l', 't', 'u', 'X', '1', '6', 0,
  /* 2959 */ 'B', 't', 'n', 'e', 'z', 'X', '1', '6', 0,
  /* 2968 */ 'B', 't', 'e', 'q', 'z', 'X', '1', '6', 0,
  /* 2977 */ 'J', 'r', 'c', 'R', 'a', '1', '6', 0,
  /* 2985 */ 'J', 'r', 'R', 'a', '1', '6', 0,
  /* 2992 */ 'R', 'e', 's', 't', 'o', 'r', 'e', '1', '6', 0,
  /* 3002 */ 'G', 'o', 't', 'P', 'r', 'o', 'l', 'o', 'g', 'u', 'e', '1', '6', 0,
  /* 3016 */ 'S', 'a', 'v', 'e', '1', '6', 0,
  /* 3023 */ 'J', 'u', 'm', 'p', 'L', 'i', 'n', 'k', 'R', 'e', 'g', '1', '6', 0,
  /* 3037 */ 'M', 'f', 'h', 'i', '1', '6', 0,
  /* 3044 */ 'B', 'r', 'e', 'a', 'k', '1', '6', 0,
  /* 3052 */ 'J', 'a', 'l', '1', '6', 0,
  /* 3058 */ 'A', 'd', 'd', 'i', 'u', 'S', 'p', 'I', 'm', 'm', '1', '6', 0,
  /* 3071 */ 'L', 'i', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3081 */ 'C', 'm', 'p', 'i', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3093 */ 'S', 'l', 't', 'i', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3105 */ 'S', 'l', 't', 'i', 'u', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3118 */ 'A', 'd', 'd', 'i', 'u', 'R', 'x', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3133 */ 'B', 'n', 'e', 'z', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3145 */ 'B', 'e', 'q', 'z', 'R', 'x', 'I', 'm', 'm', '1', '6', 0,
  /* 3157 */ 'B', 'i', 'm', 'm', '1', '6', 0,
  /* 3164 */ 'M', 'f', 'l', 'o', '1', '6', 0,
  /* 3171 */ 'L', 'w', 'R', 'x', 'P', 'c', 'T', 'c', 'p', '1', '6', 0,
  /* 3183 */ 'S', 'e', 'b', 'R', 'x', '1', '6', 0,
  /* 3191 */ 'J', 'r', 'c', 'R', 'x', '1', '6', 0,
  /* 3199 */ 'S', 'e', 'h', 'R', 'x', '1', '6', 0,
  /* 3207 */ 'S', 'l', 't', 'C', 'C', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3219 */ 'S', 'l', 't', 'u', 'C', 'C', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3232 */ 'N', 'e', 'g', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3242 */ 'C', 'm', 'p', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3252 */ 'S', 'l', 't', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3262 */ 'M', 'u', 'l', 't', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3273 */ 'N', 'o', 't', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3283 */ 'S', 'l', 't', 'u', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3294 */ 'M', 'u', 'l', 't', 'u', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3306 */ 'D', 'i', 'v', 'u', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3317 */ 'S', 'r', 'a', 'v', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3328 */ 'D', 'i', 'v', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3338 */ 'S', 'l', 'l', 'v', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3349 */ 'S', 'r', 'l', 'v', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3360 */ 'A', 'n', 'd', 'R', 'x', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3372 */ 'O', 'r', 'R', 'x', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3383 */ 'X', 'o', 'r', 'R', 'x', 'R', 'x', 'R', 'y', '1', '6', 0,
  /* 3395 */ 'M', 'u', 'l', 't', 'R', 'x', 'R', 'y', 'R', 'z', '1', '6', 0,
  /* 3408 */ 'S', 'u', 'b', 'u', 'R', 'x', 'R', 'y', 'R', 'z', '1', '6', 0,
  /* 3421 */ 'A', 'd', 'd', 'u', 'R', 'x', 'R', 'y', 'R', 'z', '1', '6', 0,
  /* 3434 */ 'S', 'l', 't', 'u', 'R', 'x', 'R', 'y', 'R', 'z', '1', '6', 0,
  /* 3447 */ 'M', 'u', 'l', 't', 'u', 'R', 'x', 'R', 'y', 'R', 'z', '1', '6', 0,
  /* 3461 */ 'B', 't', 'n', 'e', 'z', '1', '6', 0,
  /* 3469 */ 'B', 't', 'e', 'q', 'z', '1', '6', 0,
  /* 3477 */ 'L', 'D', 'C', '2', '_', 'R', '6', 0,
  /* 3485 */ 'S', 'D', 'C', '2', '_', 'R', '6', 0,
  /* 3493 */ 'L', 'W', 'C', '2', '_', 'R', '6', 0,
  /* 3501 */ 'S', 'W', 'C', '2', '_', 'R', '6', 0,
  /* 3509 */ 'D', 'L', 'S', 'A', '_', 'R', '6', 0,
  /* 3517 */ 'J', 'R', '_', 'H', 'B', '_', 'R', '6', 0,
  /* 3526 */ 'S', 'C', '_', 'R', '6', 0,
  /* 3532 */ 'S', 'C', 'D', '_', 'R', '6', 0,
  /* 3539 */ 'L', 'L', 'D', '_', 'R', '6', 0,
  /* 3546 */ 'C', 'A', 'C', 'H', 'E', '_', 'R', '6', 0,
  /* 3555 */ 'P', 'R', 'E', 'F', '_', 'R', '6', 0,
  /* 3563 */ 'L', 'L', '_', 'R', '6', 0,
  /* 3569 */ 'D', 'M', 'U', 'L', '_', 'R', '6', 0,
  /* 3577 */ 'D', 'C', 'L', 'O', '_', 'R', '6', 0,
  /* 3585 */ 'S', 'D', 'B', 'B', 'P', '_', 'R', '6', 0,
  /* 3594 */ 'D', 'C', 'L', 'Z', '_', 'R', '6', 0,
  /* 3602 */ 'L', 'O', 'A', 'D', '_', 'A', 'C', 'C', '1', '2', '8', 0,
  /* 3614 */ 'S', 'T', 'O', 'R', 'E', '_', 'A', 'C', 'C', '1', '2', '8', 0,
  /* 3627 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'S', 'U', 'B', '_', 'I', '8', 0,
  /* 3646 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'D', 'D', '_', 'I', '8', 0,
  /* 3665 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'N', 'A', 'N', 'D', '_', 'I', '8', 0,
  /* 3685 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'A', 'N', 'D', '_', 'I', '8', 0,
  /* 3704 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'S', 'W', 'A', 'P', '_', 'I', '8', 0,
  /* 3719 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'C', 'M', 'P', '_', 'S', 'W', 'A', 'P', '_', 'I', '8', 0,
  /* 3738 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'X', 'O', 'R', '_', 'I', '8', 0,
  /* 3757 */ 'A', 'T', 'O', 'M', 'I', 'C', '_', 'L', 'O', 'A', 'D', '_', 'O', 'R', '_', 'I', '8', 0,
  /* 3775 */ 'P', 'R', 'E', 'C', 'E', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'L', 'A', 0,
  /* 3790 */ 'P', 'R', 'E', 'C', 'E', 'Q', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'L', 'A', 0,
  /* 3806 */ 'P', 'R', 'E', 'C', 'E', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'R', 'A', 0,
  /* 3821 */ 'P', 'R', 'E', 'C', 'E', 'Q', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'R', 'A', 0,
  /* 3837 */ 'D', 'S', 'R', 'A', 0,
  /* 3842 */ 'R', 'e', 't', 'R', 'A', 0,
  /* 3848 */ 'D', 'L', 'S', 'A', 0,
  /* 3853 */ 'C', 'F', 'C', 'M', 'S', 'A', 0,
  /* 3860 */ 'C', 'T', 'C', 'M', 'S', 'A', 0,
  /* 3867 */ 'S', 'E', 'B', 0,
  /* 3871 */ 'E', 'H', 'B', 0,
  /* 3875 */ 'J', 'R', '_', 'H', 'B', 0,
  /* 3881 */ 'J', 'A', 'L', 'R', '_', 'H', 'B', 0,
  /* 3889 */ 'L', 'B', 0,
  /* 3892 */ 'S', 'H', 'R', 'A', '_', 'Q', 'B', 0,
  /* 3900 */ 'C', 'M', 'P', 'G', 'D', 'U', '_', 'L', 'E', '_', 'Q', 'B', 0,
  /* 3913 */ 'C', 'M', 'P', 'G', 'U', '_', 'L', 'E', '_', 'Q', 'B', 0,
  /* 3925 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'M', 'P', 'U', '_', 'L', 'E', '_', 'Q', 'B', 0,
  /* 3942 */ 'S', 'U', 'B', 'U', 'H', '_', 'Q', 'B', 0,
  /* 3951 */ 'A', 'D', 'D', 'U', 'H', '_', 'Q', 'B', 0,
  /* 3960 */ 'P', 's', 'e', 'u', 'd', 'o', 'P', 'I', 'C', 'K', '_', 'Q', 'B', 0,
  /* 3974 */ 'S', 'H', 'L', 'L', '_', 'Q', 'B', 0,
  /* 3982 */ 'R', 'E', 'P', 'L', '_', 'Q', 'B', 0,
  /* 3990 */ 'S', 'H', 'R', 'L', '_', 'Q', 'B', 0,
  /* 3998 */ 'C', 'M', 'P', 'G', 'D', 'U', '_', 'E', 'Q', '_', 'Q', 'B', 0,
  /* 4011 */ 'C', 'M', 'P', 'G', 'U', '_', 'E', 'Q', '_', 'Q', 'B', 0,
  /* 4023 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'M', 'P', 'U', '_', 'E', 'Q', '_', 'Q', 'B', 0,
  /* 4040 */ 'S', 'H', 'R', 'A', '_', 'R', '_', 'Q', 'B', 0,
  /* 4050 */ 'S', 'U', 'B', 'U', 'H', '_', 'R', '_', 'Q', 'B', 0,
  /* 4061 */ 'A', 'D', 'D', 'U', 'H', '_', 'R', '_', 'Q', 'B', 0,
  /* 4072 */ 'S', 'H', 'R', 'A', 'V', '_', 'R', '_', 'Q', 'B', 0,
  /* 4083 */ 'A', 'B', 'S', 'Q', '_', 'S', '_', 'Q', 'B', 0,
  /* 4093 */ 'S', 'U', 'B', 'U', '_', 'S', '_', 'Q', 'B', 0,
  /* 4103 */ 'A', 'D', 'D', 'U', '_', 'S', '_', 'Q', 'B', 0,
  /* 4113 */ 'C', 'M', 'P', 'G', 'D', 'U', '_', 'L', 'T', '_', 'Q', 'B', 0,
  /* 4126 */ 'C', 'M', 'P', 'G', 'U', '_', 'L', 'T', '_', 'Q', 'B', 0,
  /* 4138 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'M', 'P', 'U', '_', 'L', 'T', '_', 'Q', 'B', 0,
  /* 4155 */ 'S', 'U', 'B', 'U', '_', 'Q', 'B', 0,
  /* 4163 */ 'A', 'D', 'D', 'U', '_', 'Q', 'B', 0,
  /* 4171 */ 'S', 'H', 'R', 'A', 'V', '_', 'Q', 'B', 0,
  /* 4180 */ 'S', 'H', 'L', 'L', 'V', '_', 'Q', 'B', 0,
  /* 4189 */ 'R', 'E', 'P', 'L', 'V', '_', 'Q', 'B', 0,
  /* 4198 */ 'S', 'H', 'R', 'L', 'V', '_', 'Q', 'B', 0,
  /* 4207 */ 'R', 'A', 'D', 'D', 'U', '_', 'W', '_', 'Q', 'B', 0,
  /* 4218 */ 'S', 'B', 0,
  /* 4221 */ 'M', 'O', 'D', 'S', 'U', 'B', 0,
  /* 4228 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'S', 'U', 'B', 0,
  /* 4239 */ 'S', 'R', 'A', '_', 'B', 0,
  /* 4245 */ 'A', 'D', 'D', '_', 'A', '_', 'B', 0,
  /* 4253 */ 'M', 'I', 'N', '_', 'A', '_', 'B', 0,
  /* 4261 */ 'A', 'D', 'D', 'S', '_', 'A', '_', 'B', 0,
  /* 4270 */ 'M', 'A', 'X', '_', 'A', '_', 'B', 0,
  /* 4278 */ 'N', 'L', 'O', 'C', '_', 'B', 0,
  /* 4285 */ 'N', 'L', 'Z', 'C', '_', 'B', 0,
  /* 4292 */ 'S', 'L', 'D', '_', 'B', 0,
  /* 4298 */ 'P', 'C', 'K', 'O', 'D', '_', 'B', 0,
  /* 4306 */ 'I', 'L', 'V', 'O', 'D', '_', 'B', 0,
  /* 4314 */ 'I', 'N', 'S', 'V', 'E', '_', 'B', 0,
  /* 4322 */ 'V', 'S', 'H', 'F', '_', 'B', 0,
  /* 4329 */ 'B', 'N', 'E', 'G', '_', 'B', 0,
  /* 4336 */ 'S', 'R', 'A', 'I', '_', 'B', 0,
  /* 4343 */ 'S', 'L', 'D', 'I', '_', 'B', 0,
  /* 4350 */ 'A', 'N', 'D', 'I', '_', 'B', 0,
  /* 4357 */ 'B', 'N', 'E', 'G', 'I', '_', 'B', 0,
  /* 4365 */ 'B', 'S', 'E', 'L', 'I', '_', 'B', 0,
  /* 4373 */ 'S', 'L', 'L', 'I', '_', 'B', 0,
  /* 4380 */ 'S', 'R', 'L', 'I', '_', 'B', 0,
  /* 4387 */ 'B', 'I', 'N', 'S', 'L', 'I', '_', 'B', 0,
  /* 4396 */ 'C', 'E', 'Q', 'I', '_', 'B', 0,
  /* 4403 */ 'S', 'R', 'A', 'R', 'I', '_', 'B', 0,
  /* 4411 */ 'B', 'C', 'L', 'R', 'I', '_', 'B', 0,
  /* 4419 */ 'S', 'R', 'L', 'R', 'I', '_', 'B', 0,
  /* 4427 */ 'N', 'O', 'R', 'I', '_', 'B', 0,
  /* 4434 */ 'X', 'O', 'R', 'I', '_', 'B', 0,
  /* 4441 */ 'B', 'I', 'N', 'S', 'R', 'I', '_', 'B', 0,
  /* 4450 */ 'S', 'P', 'L', 'A', 'T', 'I', '_', 'B', 0,
  /* 4459 */ 'B', 'S', 'E', 'T', 'I', '_', 'B', 0,
  /* 4467 */ 'S', 'U', 'B', 'V', 'I', '_', 'B', 0,
  /* 4475 */ 'A', 'D', 'D', 'V', 'I', '_', 'B', 0,
  /* 4483 */ 'B', 'M', 'Z', 'I', '_', 'B', 0,
  /* 4490 */ 'B', 'M', 'N', 'Z', 'I', '_', 'B', 0,
  /* 4498 */ 'F', 'I', 'L', 'L', '_', 'B', 0,
  /* 4505 */ 'S', 'L', 'L', '_', 'B', 0,
  /* 4511 */ 'S', 'R', 'L', '_', 'B', 0,
  /* 4517 */ 'B', 'I', 'N', 'S', 'L', '_', 'B', 0,
  /* 4525 */ 'I', 'L', 'V', 'L', '_', 'B', 0,
  /* 4532 */ 'C', 'E', 'Q', '_', 'B', 0,
  /* 4538 */ 'S', 'R', 'A', 'R', '_', 'B', 0,
  /* 4545 */ 'B', 'C', 'L', 'R', '_', 'B', 0,
  /* 4552 */ 'S', 'R', 'L', 'R', '_', 'B', 0,
  /* 4559 */ 'B', 'I', 'N', 'S', 'R', '_', 'B', 0,
  /* 4567 */ 'I', 'L', 'V', 'R', '_', 'B', 0,
  /* 4574 */ 'A', 'S', 'U', 'B', '_', 'S', '_', 'B', 0,
  /* 4583 */ 'M', 'O', 'D', '_', 'S', '_', 'B', 0,
  /* 4591 */ 'C', 'L', 'E', '_', 'S', '_', 'B', 0,
  /* 4599 */ 'A', 'V', 'E', '_', 'S', '_', 'B', 0,
  /* 4607 */ 'C', 'L', 'E', 'I', '_', 'S', '_', 'B', 0,
  /* 4616 */ 'M', 'I', 'N', 'I', '_', 'S', '_', 'B', 0,
  /* 4625 */ 'C', 'L', 'T', 'I', '_', 'S', '_', 'B', 0,
  /* 4634 */ 'M', 'A', 'X', 'I', '_', 'S', '_', 'B', 0,
  /* 4643 */ 'M', 'I', 'N', '_', 'S', '_', 'B', 0,
  /* 4651 */ 'A', 'V', 'E', 'R', '_', 'S', '_', 'B', 0,
  /* 4660 */ 'S', 'U', 'B', 'S', '_', 'S', '_', 'B', 0,
  /* 4669 */ 'A', 'D', 'D', 'S', '_', 'S', '_', 'B', 0,
  /* 4678 */ 'S', 'A', 'T', '_', 'S', '_', 'B', 0,
  /* 4686 */ 'C', 'L', 'T', '_', 'S', '_', 'B', 0,
  /* 4694 */ 'S', 'U', 'B', 'S', 'U', 'U', '_', 'S', '_', 'B', 0,
  /* 4705 */ 'D', 'I', 'V', '_', 'S', '_', 'B', 0,
  /* 4713 */ 'M', 'A', 'X', '_', 'S', '_', 'B', 0,
  /* 4721 */ 'C', 'O', 'P', 'Y', '_', 'S', '_', 'B', 0,
  /* 4730 */ 'S', 'P', 'L', 'A', 'T', '_', 'B', 0,
  /* 4738 */ 'B', 'S', 'E', 'T', '_', 'B', 0,
  /* 4745 */ 'P', 'C', 'N', 'T', '_', 'B', 0,
  /* 4752 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'B', 0,
  /* 4761 */ 'S', 'T', '_', 'B', 0,
  /* 4766 */ 'A', 'S', 'U', 'B', '_', 'U', '_', 'B', 0,
  /* 4775 */ 'M', 'O', 'D', '_', 'U', '_', 'B', 0,
  /* 4783 */ 'C', 'L', 'E', '_', 'U', '_', 'B', 0,
  /* 4791 */ 'A', 'V', 'E', '_', 'U', '_', 'B', 0,
  /* 4799 */ 'C', 'L', 'E', 'I', '_', 'U', '_', 'B', 0,
  /* 4808 */ 'M', 'I', 'N', 'I', '_', 'U', '_', 'B', 0,
  /* 4817 */ 'C', 'L', 'T', 'I', '_', 'U', '_', 'B', 0,
  /* 4826 */ 'M', 'A', 'X', 'I', '_', 'U', '_', 'B', 0,
  /* 4835 */ 'M', 'I', 'N', '_', 'U', '_', 'B', 0,
  /* 4843 */ 'A', 'V', 'E', 'R', '_', 'U', '_', 'B', 0,
  /* 4852 */ 'S', 'U', 'B', 'S', '_', 'U', '_', 'B', 0,
  /* 4861 */ 'A', 'D', 'D', 'S', '_', 'U', '_', 'B', 0,
  /* 4870 */ 'S', 'U', 'B', 'S', 'U', 'S', '_', 'U', '_', 'B', 0,
  /* 4881 */ 'S', 'A', 'T', '_', 'U', '_', 'B', 0,
  /* 4889 */ 'C', 'L', 'T', '_', 'U', '_', 'B', 0,
  /* 4897 */ 'D', 'I', 'V', '_', 'U', '_', 'B', 0,
  /* 4905 */ 'M', 'A', 'X', '_', 'U', '_', 'B', 0,
  /* 4913 */ 'C', 'O', 'P', 'Y', '_', 'U', '_', 'B', 0,
  /* 4922 */ 'M', 'S', 'U', 'B', 'V', '_', 'B', 0,
  /* 4930 */ 'M', 'A', 'D', 'D', 'V', '_', 'B', 0,
  /* 4938 */ 'P', 'C', 'K', 'E', 'V', '_', 'B', 0,
  /* 4946 */ 'I', 'L', 'V', 'E', 'V', '_', 'B', 0,
  /* 4954 */ 'M', 'U', 'L', 'V', '_', 'B', 0,
  /* 4961 */ 'B', 'Z', '_', 'B', 0,
  /* 4966 */ 'B', 'N', 'Z', '_', 'B', 0,
  /* 4972 */ 'B', 'C', 0,
  /* 4975 */ 'B', 'G', 'E', 'C', 0,
  /* 4980 */ 'B', 'N', 'E', 'C', 0,
  /* 4985 */ 'J', 'I', 'C', 0,
  /* 4989 */ 'B', 'A', 'L', 'C', 0,
  /* 4994 */ 'J', 'I', 'A', 'L', 'C', 0,
  /* 5000 */ 'B', 'G', 'E', 'Z', 'A', 'L', 'C', 0,
  /* 5008 */ 'B', 'L', 'E', 'Z', 'A', 'L', 'C', 0,
  /* 5016 */ 'B', 'N', 'E', 'Z', 'A', 'L', 'C', 0,
  /* 5024 */ 'B', 'E', 'Q', 'Z', 'A', 'L', 'C', 0,
  /* 5032 */ 'B', 'G', 'T', 'Z', 'A', 'L', 'C', 0,
  /* 5040 */ 'B', 'L', 'T', 'Z', 'A', 'L', 'C', 0,
  /* 5048 */ 'S', 'Y', 'N', 'C', 0,
  /* 5053 */ 'F', 'R', 'A', 'M', 'E', '_', 'A', 'L', 'L', 'O', 'C', 0,
  /* 5065 */ 'L', 'D', 'P', 'C', 0,
  /* 5070 */ 'A', 'U', 'I', 'P', 'C', 0,
  /* 5076 */ 'A', 'L', 'U', 'I', 'P', 'C', 0,
  /* 5083 */ 'A', 'D', 'D', 'I', 'U', 'P', 'C', 0,
  /* 5091 */ 'L', 'W', 'U', 'P', 'C', 0,
  /* 5097 */ 'L', 'W', 'P', 'C', 0,
  /* 5102 */ 'B', 'E', 'Q', 'C', 0,
  /* 5107 */ 'A', 'D', 'D', 'S', 'C', 0,
  /* 5113 */ 'B', 'L', 'T', 'C', 0,
  /* 5118 */ 'B', 'G', 'E', 'U', 'C', 0,
  /* 5124 */ 'B', 'L', 'T', 'U', 'C', 0,
  /* 5130 */ 'B', 'N', 'V', 'C', 0,
  /* 5135 */ 'B', 'O', 'V', 'C', 0,
  /* 5140 */ 'A', 'D', 'D', 'W', 'C', 0,
  /* 5146 */ 'B', 'G', 'E', 'Z', 'C', 0,
  /* 5152 */ 'B', 'L', 'E', 'Z', 'C', 0,
  /* 5158 */ 'B', 'N', 'E', 'Z', 'C', 0,
  /* 5164 */ 'B', 'E', 'Q', 'Z', 'C', 0,
  /* 5170 */ 'B', 'G', 'T', 'Z', 'C', 0,
  /* 5176 */ 'B', 'L', 'T', 'Z', 'C', 0,
  /* 5182 */ 'S', 'C', 'D', 0,
  /* 5186 */ 'D', 'A', 'D', 'D', 0,
  /* 5191 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'A', 'D', 'D', 0,
  /* 5202 */ 'D', 'S', 'H', 'D', 0,
  /* 5207 */ 'L', 'L', 'D', 0,
  /* 5211 */ 'A', 'N', 'D', 0,
  /* 5215 */ 'P', 'R', 'E', 'P', 'E', 'N', 'D', 0,
  /* 5223 */ 'A', 'P', 'P', 'E', 'N', 'D', 0,
  /* 5230 */ 'L', 'I', 'F', 'E', 'T', 'I', 'M', 'E', '_', 'E', 'N', 'D', 0,
  /* 5243 */ 'D', 'M', 'O', 'D', 0,
  /* 5248 */ 'L', 'O', 'A', 'D', '_', 'S', 'T', 'A', 'C', 'K', '_', 'G', 'U', 'A', 'R', 'D', 0,
  /* 5265 */ 'S', 'D', 0,
  /* 5268 */ 'F', 'L', 'O', 'G', '2', '_', 'D', 0,
  /* 5276 */ 'F', 'E', 'X', 'P', '2', '_', 'D', 0,
  /* 5284 */ 'M', 'I', 'N', 'A', '_', 'D', 0,
  /* 5291 */ 'S', 'R', 'A', '_', 'D', 0,
  /* 5297 */ 'M', 'A', 'X', 'A', '_', 'D', 0,
  /* 5304 */ 'A', 'D', 'D', '_', 'A', '_', 'D', 0,
  /* 5312 */ 'F', 'M', 'I', 'N', '_', 'A', '_', 'D', 0,
  /* 5321 */ 'A', 'D', 'D', 'S', '_', 'A', '_', 'D', 0,
  /* 5330 */ 'F', 'M', 'A', 'X', '_', 'A', '_', 'D', 0,
  /* 5339 */ 'F', 'S', 'U', 'B', '_', 'D', 0,
  /* 5346 */ 'F', 'M', 'S', 'U', 'B', '_', 'D', 0,
  /* 5354 */ 'N', 'L', 'O', 'C', '_', 'D', 0,
  /* 5361 */ 'N', 'L', 'Z', 'C', '_', 'D', 0,
  /* 5368 */ 'F', 'A', 'D', 'D', '_', 'D', 0,
  /* 5375 */ 'F', 'M', 'A', 'D', 'D', '_', 'D', 0,
  /* 5383 */ 'S', 'L', 'D', '_', 'D', 0,
  /* 5389 */ 'P', 'C', 'K', 'O', 'D', '_', 'D', 0,
  /* 5397 */ 'I', 'L', 'V', 'O', 'D', '_', 'D', 0,
  /* 5405 */ 'F', 'C', 'L', 'E', '_', 'D', 0,
  /* 5412 */ 'F', 'S', 'L', 'E', '_', 'D', 0,
  /* 5419 */ 'C', 'M', 'P', '_', 'S', 'L', 'E', '_', 'D', 0,
  /* 5429 */ 'F', 'C', 'U', 'L', 'E', '_', 'D', 0,
  /* 5437 */ 'F', 'S', 'U', 'L', 'E', '_', 'D', 0,
  /* 5445 */ 'C', 'M', 'P', '_', 'S', 'U', 'L', 'E', '_', 'D', 0,
  /* 5456 */ 'C', 'M', 'P', '_', 'U', 'L', 'E', '_', 'D', 0,
  /* 5466 */ 'C', 'M', 'P', '_', 'L', 'E', '_', 'D', 0,
  /* 5475 */ 'F', 'C', 'N', 'E', '_', 'D', 0,
  /* 5482 */ 'F', 'S', 'N', 'E', '_', 'D', 0,
  /* 5489 */ 'F', 'C', 'U', 'N', 'E', '_', 'D', 0,
  /* 5497 */ 'F', 'S', 'U', 'N', 'E', '_', 'D', 0,
  /* 5505 */ 'I', 'N', 'S', 'V', 'E', '_', 'D', 0,
  /* 5513 */ 'F', 'C', 'A', 'F', '_', 'D', 0,
  /* 5520 */ 'F', 'S', 'A', 'F', '_', 'D', 0,
  /* 5527 */ 'C', 'M', 'P', '_', 'S', 'A', 'F', '_', 'D', 0,
  /* 5537 */ 'M', 'S', 'U', 'B', 'F', '_', 'D', 0,
  /* 5545 */ 'M', 'A', 'D', 'D', 'F', '_', 'D', 0,
  /* 5553 */ 'V', 'S', 'H', 'F', '_', 'D', 0,
  /* 5560 */ 'C', 'M', 'P', '_', 'F', '_', 'D', 0,
  /* 5568 */ 'B', 'N', 'E', 'G', '_', 'D', 0,
  /* 5575 */ 'S', 'R', 'A', 'I', '_', 'D', 0,
  /* 5582 */ 'S', 'L', 'D', 'I', '_', 'D', 0,
  /* 5589 */ 'B', 'N', 'E', 'G', 'I', '_', 'D', 0,
  /* 5597 */ 'S', 'L', 'L', 'I', '_', 'D', 0,
  /* 5604 */ 'S', 'R', 'L', 'I', '_', 'D', 0,
  /* 5611 */ 'B', 'I', 'N', 'S', 'L', 'I', '_', 'D', 0,
  /* 5620 */ 'C', 'E', 'Q', 'I', '_', 'D', 0,
  /* 5627 */ 'S', 'R', 'A', 'R', 'I', '_', 'D', 0,
  /* 5635 */ 'B', 'C', 'L', 'R', 'I', '_', 'D', 0,
  /* 5643 */ 'S', 'R', 'L', 'R', 'I', '_', 'D', 0,
  /* 5651 */ 'B', 'I', 'N', 'S', 'R', 'I', '_', 'D', 0,
  /* 5660 */ 'S', 'P', 'L', 'A', 'T', 'I', '_', 'D', 0,
  /* 5669 */ 'B', 'S', 'E', 'T', 'I', '_', 'D', 0,
  /* 5677 */ 'S', 'U', 'B', 'V', 'I', '_', 'D', 0,
  /* 5685 */ 'A', 'D', 'D', 'V', 'I', '_', 'D', 0,
  /* 5693 */ 'S', 'E', 'L', '_', 'D', 0,
  /* 5699 */ 'F', 'I', 'L', 'L', '_', 'D', 0,
  /* 5706 */ 'S', 'L', 'L', '_', 'D', 0,
  /* 5712 */ 'F', 'E', 'X', 'U', 'P', 'L', '_', 'D', 0,
  /* 5721 */ 'F', 'F', 'Q', 'L', '_', 'D', 0,
  /* 5728 */ 'S', 'R', 'L', '_', 'D', 0,
  /* 5734 */ 'B', 'I', 'N', 'S', 'L', '_', 'D', 0,
  /* 5742 */ 'F', 'M', 'U', 'L', '_', 'D', 0,
  /* 5749 */ 'I', 'L', 'V', 'L', '_', 'D', 0,
  /* 5756 */ 'F', 'M', 'I', 'N', '_', 'D', 0,
  /* 5763 */ 'F', 'C', 'U', 'N', '_', 'D', 0,
  /* 5770 */ 'F', 'S', 'U', 'N', '_', 'D', 0,
  /* 5777 */ 'C', 'M', 'P', '_', 'S', 'U', 'N', '_', 'D', 0,
  /* 5787 */ 'C', 'M', 'P', '_', 'U', 'N', '_', 'D', 0,
  /* 5796 */ 'F', 'R', 'C', 'P', '_', 'D', 0,
  /* 5803 */ 'F', 'C', 'E', 'Q', '_', 'D', 0,
  /* 5810 */ 'F', 'S', 'E', 'Q', '_', 'D', 0,
  /* 5817 */ 'C', 'M', 'P', '_', 'S', 'E', 'Q', '_', 'D', 0,
  /* 5827 */ 'F', 'C', 'U', 'E', 'Q', '_', 'D', 0,
  /* 5835 */ 'F', 'S', 'U', 'E', 'Q', '_', 'D', 0,
  /* 5843 */ 'C', 'M', 'P', '_', 'S', 'U', 'E', 'Q', '_', 'D', 0,
  /* 5854 */ 'C', 'M', 'P', '_', 'U', 'E', 'Q', '_', 'D', 0,
  /* 5864 */ 'C', 'M', 'P', '_', 'E', 'Q', '_', 'D', 0,
  /* 5873 */ 'S', 'R', 'A', 'R', '_', 'D', 0,
  /* 5880 */ 'B', 'C', 'L', 'R', '_', 'D', 0,
  /* 5887 */ 'S', 'R', 'L', 'R', '_', 'D', 0,
  /* 5894 */ 'F', 'C', 'O', 'R', '_', 'D', 0,
  /* 5901 */ 'F', 'S', 'O', 'R', '_', 'D', 0,
  /* 5908 */ 'F', 'E', 'X', 'U', 'P', 'R', '_', 'D', 0,
  /* 5917 */ 'F', 'F', 'Q', 'R', '_', 'D', 0,
  /* 5924 */ 'B', 'I', 'N', 'S', 'R', '_', 'D', 0,
  /* 5932 */ 'I', 'L', 'V', 'R', '_', 'D', 0,
  /* 5939 */ 'F', 'A', 'B', 'S', '_', 'D', 0,
  /* 5946 */ 'F', 'C', 'L', 'A', 'S', 'S', '_', 'D', 0,
  /* 5955 */ 'A', 'S', 'U', 'B', '_', 'S', '_', 'D', 0,
  /* 5964 */ 'H', 'S', 'U', 'B', '_', 'S', '_', 'D', 0,
  /* 5973 */ 'D', 'P', 'S', 'U', 'B', '_', 'S', '_', 'D', 0,
  /* 5983 */ 'F', 'T', 'R', 'U', 'N', 'C', '_', 'S', '_', 'D', 0,
  /* 5994 */ 'H', 'A', 'D', 'D', '_', 'S', '_', 'D', 0,
  /* 6003 */ 'D', 'P', 'A', 'D', 'D', '_', 'S', '_', 'D', 0,
  /* 6013 */ 'M', 'O', 'D', '_', 'S', '_', 'D', 0,
  /* 6021 */ 'C', 'L', 'E', '_', 'S', '_', 'D', 0,
  /* 6029 */ 'A', 'V', 'E', '_', 'S', '_', 'D', 0,
  /* 6037 */ 'C', 'L', 'E', 'I', '_', 'S', '_', 'D', 0,
  /* 6046 */ 'M', 'I', 'N', 'I', '_', 'S', '_', 'D', 0,
  /* 6055 */ 'C', 'L', 'T', 'I', '_', 'S', '_', 'D', 0,
  /* 6064 */ 'M', 'A', 'X', 'I', '_', 'S', '_', 'D', 0,
  /* 6073 */ 'M', 'I', 'N', '_', 'S', '_', 'D', 0,
  /* 6081 */ 'D', 'O', 'T', 'P', '_', 'S', '_', 'D', 0,
  /* 6090 */ 'A', 'V', 'E', 'R', '_', 'S', '_', 'D', 0,
  /* 6099 */ 'S', 'U', 'B', 'S', '_', 'S', '_', 'D', 0,
  /* 6108 */ 'A', 'D', 'D', 'S', '_', 'S', '_', 'D', 0,
  /* 6117 */ 'S', 'A', 'T', '_', 'S', '_', 'D', 0,
  /* 6125 */ 'C', 'L', 'T', '_', 'S', '_', 'D', 0,
  /* 6133 */ 'F', 'F', 'I', 'N', 'T', '_', 'S', '_', 'D', 0,
  /* 6143 */ 'F', 'T', 'I', 'N', 'T', '_', 'S', '_', 'D', 0,
  /* 6153 */ 'S', 'U', 'B', 'S', 'U', 'U', '_', 'S', '_', 'D', 0,
  /* 6164 */ 'D', 'I', 'V', '_', 'S', '_', 'D', 0,
  /* 6172 */ 'M', 'A', 'X', '_', 'S', '_', 'D', 0,
  /* 6180 */ 'C', 'O', 'P', 'Y', '_', 'S', '_', 'D', 0,
  /* 6189 */ 'S', 'P', 'L', 'A', 'T', '_', 'D', 0,
  /* 6197 */ 'B', 'S', 'E', 'T', '_', 'D', 0,
  /* 6204 */ 'F', 'C', 'L', 'T', '_', 'D', 0,
  /* 6211 */ 'F', 'S', 'L', 'T', '_', 'D', 0,
  /* 6218 */ 'C', 'M', 'P', '_', 'S', 'L', 'T', '_', 'D', 0,
  /* 6228 */ 'F', 'C', 'U', 'L', 'T', '_', 'D', 0,
  /* 6236 */ 'F', 'S', 'U', 'L', 'T', '_', 'D', 0,
  /* 6244 */ 'C', 'M', 'P', '_', 'S', 'U', 'L', 'T', '_', 'D', 0,
  /* 6255 */ 'C', 'M', 'P', '_', 'U', 'L', 'T', '_', 'D', 0,
  /* 6265 */ 'C', 'M', 'P', '_', 'L', 'T', '_', 'D', 0,
  /* 6274 */ 'P', 'C', 'N', 'T', '_', 'D', 0,
  /* 6281 */ 'F', 'R', 'I', 'N', 'T', '_', 'D', 0,
  /* 6289 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'D', 0,
  /* 6298 */ 'F', 'S', 'Q', 'R', 'T', '_', 'D', 0,
  /* 6306 */ 'F', 'R', 'S', 'Q', 'R', 'T', '_', 'D', 0,
  /* 6315 */ 'S', 'T', '_', 'D', 0,
  /* 6320 */ 'A', 'S', 'U', 'B', '_', 'U', '_', 'D', 0,
  /* 6329 */ 'H', 'S', 'U', 'B', '_', 'U', '_', 'D', 0,
  /* 6338 */ 'D', 'P', 'S', 'U', 'B', '_', 'U', '_', 'D', 0,
  /* 6348 */ 'F', 'T', 'R', 'U', 'N', 'C', '_', 'U', '_', 'D', 0,
  /* 6359 */ 'H', 'A', 'D', 'D', '_', 'U', '_', 'D', 0,
  /* 6368 */ 'D', 'P', 'A', 'D', 'D', '_', 'U', '_', 'D', 0,
  /* 6378 */ 'M', 'O', 'D', '_', 'U', '_', 'D', 0,
  /* 6386 */ 'C', 'L', 'E', '_', 'U', '_', 'D', 0,
  /* 6394 */ 'A', 'V', 'E', '_', 'U', '_', 'D', 0,
  /* 6402 */ 'C', 'L', 'E', 'I', '_', 'U', '_', 'D', 0,
  /* 6411 */ 'M', 'I', 'N', 'I', '_', 'U', '_', 'D', 0,
  /* 6420 */ 'C', 'L', 'T', 'I', '_', 'U', '_', 'D', 0,
  /* 6429 */ 'M', 'A', 'X', 'I', '_', 'U', '_', 'D', 0,
  /* 6438 */ 'M', 'I', 'N', '_', 'U', '_', 'D', 0,
  /* 6446 */ 'D', 'O', 'T', 'P', '_', 'U', '_', 'D', 0,
  /* 6455 */ 'A', 'V', 'E', 'R', '_', 'U', '_', 'D', 0,
  /* 6464 */ 'S', 'U', 'B', 'S', '_', 'U', '_', 'D', 0,
  /* 6473 */ 'A', 'D', 'D', 'S', '_', 'U', '_', 'D', 0,
  /* 6482 */ 'S', 'U', 'B', 'S', 'U', 'S', '_', 'U', '_', 'D', 0,
  /* 6493 */ 'S', 'A', 'T', '_', 'U', '_', 'D', 0,
  /* 6501 */ 'C', 'L', 'T', '_', 'U', '_', 'D', 0,
  /* 6509 */ 'F', 'F', 'I', 'N', 'T', '_', 'U', '_', 'D', 0,
  /* 6519 */ 'F', 'T', 'I', 'N', 'T', '_', 'U', '_', 'D', 0,
  /* 6529 */ 'D', 'I', 'V', '_', 'U', '_', 'D', 0,
  /* 6537 */ 'M', 'A', 'X', '_', 'U', '_', 'D', 0,
  /* 6545 */ 'C', 'O', 'P', 'Y', '_', 'U', '_', 'D', 0,
  /* 6554 */ 'M', 'S', 'U', 'B', 'V', '_', 'D', 0,
  /* 6562 */ 'M', 'A', 'D', 'D', 'V', '_', 'D', 0,
  /* 6570 */ 'P', 'C', 'K', 'E', 'V', '_', 'D', 0,
  /* 6578 */ 'I', 'L', 'V', 'E', 'V', '_', 'D', 0,
  /* 6586 */ 'F', 'D', 'I', 'V', '_', 'D', 0,
  /* 6593 */ 'M', 'U', 'L', 'V', '_', 'D', 0,
  /* 6600 */ 'F', 'M', 'A', 'X', '_', 'D', 0,
  /* 6607 */ 'B', 'Z', '_', 'D', 0,
  /* 6612 */ 'S', 'E', 'L', 'N', 'E', 'Z', '_', 'D', 0,
  /* 6621 */ 'B', 'N', 'Z', '_', 'D', 0,
  /* 6627 */ 'S', 'E', 'L', 'E', 'Q', 'Z', '_', 'D', 0,
  /* 6636 */ 'R', 'E', 'G', '_', 'S', 'E', 'Q', 'U', 'E', 'N', 'C', 'E', 0,
  /* 6649 */ 'T', 'G', 'E', 0,
  /* 6653 */ 'C', 'A', 'C', 'H', 'E', 0,
  /* 6659 */ 'B', 'U', 'N', 'D', 'L', 'E', 0,
  /* 6666 */ 'B', 'N', 'E', 0,
  /* 6670 */ 'S', 'N', 'E', 0,
  /* 6674 */ 'T', 'N', 'E', 0,
  /* 6678 */ 'P', 'A', 'U', 'S', 'E', 0,
  /* 6684 */ 'D', 'B', 'G', '_', 'V', 'A', 'L', 'U', 'E', 0,
  /* 6694 */ 'B', 'C', '1', 'F', 0,
  /* 6699 */ 'I', 'M', 'P', 'L', 'I', 'C', 'I', 'T', '_', 'D', 'E', 'F', 0,
  /* 6712 */ 'P', 'R', 'E', 'F', 0,
  /* 6717 */ 'E', 'X', 'T', 'R', 'A', 'C', 'T', '_', 'S', 'U', 'B', 'R', 'E', 'G', 0,
  /* 6732 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'S', 'U', 'B', 'R', 'E', 'G', 0,
  /* 6746 */ 'S', 'U', 'B', 'R', 'E', 'G', '_', 'T', 'O', '_', 'R', 'E', 'G', 0,
  /* 6760 */ 'D', 'S', 'B', 'H', 0,
  /* 6765 */ 'W', 'S', 'B', 'H', 0,
  /* 6770 */ 'S', 'E', 'H', 0,
  /* 6774 */ 'L', 'H', 0,
  /* 6777 */ 'S', 'H', 'R', 'A', '_', 'P', 'H', 0,
  /* 6785 */ 'P', 'R', 'E', 'C', 'R', 'Q', '_', 'Q', 'B', '_', 'P', 'H', 0,
  /* 6798 */ 'P', 'R', 'E', 'C', 'R', '_', 'Q', 'B', '_', 'P', 'H', 0,
  /* 6810 */ 'P', 'R', 'E', 'C', 'R', 'Q', 'U', '_', 'S', '_', 'Q', 'B', '_', 'P', 'H', 0,
  /* 6826 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'M', 'P', '_', 'L', 'E', '_', 'P', 'H', 0,
  /* 6842 */ 'S', 'U', 'B', 'Q', 'H', '_', 'P', 'H', 0,
  /* 6851 */ 'A', 'D', 'D', 'Q', 'H', '_', 'P', 'H', 0,
  /* 6860 */ 'P', 's', 'e', 'u', 'd', 'o', 'P', 'I', 'C', 'K', '_', 'P', 'H', 0,
  /* 6874 */ 'S', 'H', 'L', 'L', '_', 'P', 'H', 0,
  /* 6882 */ 'R', 'E', 'P', 'L', '_', 'P', 'H', 0,
  /* 6890 */ 'S', 'H', 'R', 'L', '_', 'P', 'H', 0,
  /* 6898 */ 'P', 'A', 'C', 'K', 'R', 'L', '_', 'P', 'H', 0,
  /* 6908 */ 'M', 'U', 'L', '_', 'P', 'H', 0,
  /* 6915 */ 'S', 'U', 'B', 'Q', '_', 'P', 'H', 0,
  /* 6923 */ 'A', 'D', 'D', 'Q', '_', 'P', 'H', 0,
  /* 6931 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'M', 'P', '_', 'E', 'Q', '_', 'P', 'H', 0,
  /* 6947 */ 'S', 'H', 'R', 'A', '_', 'R', '_', 'P', 'H', 0,
  /* 6957 */ 'S', 'U', 'B', 'Q', 'H', '_', 'R', '_', 'P', 'H', 0,
  /* 6968 */ 'A', 'D', 'D', 'Q', 'H', '_', 'R', '_', 'P', 'H', 0,
  /* 6979 */ 'S', 'H', 'R', 'A', 'V', '_', 'R', '_', 'P', 'H', 0,
  /* 6990 */ 'M', 'U', 'L', 'Q', '_', 'R', 'S', '_', 'P', 'H', 0,
  /* 7001 */ 'S', 'H', 'L', 'L', '_', 'S', '_', 'P', 'H', 0,
  /* 7011 */ 'M', 'U', 'L', '_', 'S', '_', 'P', 'H', 0,
  /* 7020 */ 'S', 'U', 'B', 'Q', '_', 'S', '_', 'P', 'H', 0,
  /* 7030 */ 'A', 'D', 'D', 'Q', '_', 'S', '_', 'P', 'H', 0,
  /* 7040 */ 'M', 'U', 'L', 'Q', '_', 'S', '_', 'P', 'H', 0,
  /* 7050 */ 'A', 'B', 'S', 'Q', '_', 'S', '_', 'P', 'H', 0,
  /* 7060 */ 'S', 'U', 'B', 'U', '_', 'S', '_', 'P', 'H', 0,
  /* 7070 */ 'A', 'D', 'D', 'U', '_', 'S', '_', 'P', 'H', 0,
  /* 7080 */ 'S', 'H', 'L', 'L', 'V', '_', 'S', '_', 'P', 'H', 0,
  /* 7091 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'M', 'P', '_', 'L', 'T', '_', 'P', 'H', 0,
  /* 7107 */ 'S', 'U', 'B', 'U', '_', 'P', 'H', 0,
  /* 7115 */ 'A', 'D', 'D', 'U', '_', 'P', 'H', 0,
  /* 7123 */ 'S', 'H', 'R', 'A', 'V', '_', 'P', 'H', 0,
  /* 7132 */ 'S', 'H', 'L', 'L', 'V', '_', 'P', 'H', 0,
  /* 7141 */ 'R', 'E', 'P', 'L', 'V', '_', 'P', 'H', 0,
  /* 7150 */ 'S', 'H', 'R', 'L', 'V', '_', 'P', 'H', 0,
  /* 7159 */ 'D', 'P', 'A', '_', 'W', '_', 'P', 'H', 0,
  /* 7168 */ 'M', 'U', 'L', 'S', 'A', '_', 'W', '_', 'P', 'H', 0,
  /* 7179 */ 'D', 'P', 'A', 'Q', 'X', '_', 'S', 'A', '_', 'W', '_', 'P', 'H', 0,
  /* 7193 */ 'D', 'P', 'S', 'Q', 'X', '_', 'S', 'A', '_', 'W', '_', 'P', 'H', 0,
  /* 7207 */ 'D', 'P', 'S', '_', 'W', '_', 'P', 'H', 0,
  /* 7216 */ 'D', 'P', 'A', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 0,
  /* 7228 */ 'M', 'U', 'L', 'S', 'A', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 0,
  /* 7242 */ 'D', 'P', 'S', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 0,
  /* 7254 */ 'D', 'P', 'A', 'Q', 'X', '_', 'S', '_', 'W', '_', 'P', 'H', 0,
  /* 7267 */ 'D', 'P', 'S', 'Q', 'X', '_', 'S', '_', 'W', '_', 'P', 'H', 0,
  /* 7280 */ 'D', 'P', 'A', 'X', '_', 'W', '_', 'P', 'H', 0,
  /* 7290 */ 'D', 'P', 'S', 'X', '_', 'W', '_', 'P', 'H', 0,
  /* 7300 */ 'S', 'H', 0,
  /* 7303 */ 'D', 'M', 'U', 'H', 0,
  /* 7308 */ 'S', 'R', 'A', '_', 'H', 0,
  /* 7314 */ 'A', 'D', 'D', '_', 'A', '_', 'H', 0,
  /* 7322 */ 'M', 'I', 'N', '_', 'A', '_', 'H', 0,
  /* 7330 */ 'A', 'D', 'D', 'S', '_', 'A', '_', 'H', 0,
  /* 7339 */ 'M', 'A', 'X', '_', 'A', '_', 'H', 0,
  /* 7347 */ 'N', 'L', 'O', 'C', '_', 'H', 0,
  /* 7354 */ 'N', 'L', 'Z', 'C', '_', 'H', 0,
  /* 7361 */ 'S', 'L', 'D', '_', 'H', 0,
  /* 7367 */ 'P', 'C', 'K', 'O', 'D', '_', 'H', 0,
  /* 7375 */ 'I', 'L', 'V', 'O', 'D', '_', 'H', 0,
  /* 7383 */ 'I', 'N', 'S', 'V', 'E', '_', 'H', 0,
  /* 7391 */ 'V', 'S', 'H', 'F', '_', 'H', 0,
  /* 7398 */ 'B', 'N', 'E', 'G', '_', 'H', 0,
  /* 7405 */ 'S', 'R', 'A', 'I', '_', 'H', 0,
  /* 7412 */ 'S', 'L', 'D', 'I', '_', 'H', 0,
  /* 7419 */ 'B', 'N', 'E', 'G', 'I', '_', 'H', 0,
  /* 7427 */ 'S', 'L', 'L', 'I', '_', 'H', 0,
  /* 7434 */ 'S', 'R', 'L', 'I', '_', 'H', 0,
  /* 7441 */ 'B', 'I', 'N', 'S', 'L', 'I', '_', 'H', 0,
  /* 7450 */ 'C', 'E', 'Q', 'I', '_', 'H', 0,
  /* 7457 */ 'S', 'R', 'A', 'R', 'I', '_', 'H', 0,
  /* 7465 */ 'B', 'C', 'L', 'R', 'I', '_', 'H', 0,
  /* 7473 */ 'S', 'R', 'L', 'R', 'I', '_', 'H', 0,
  /* 7481 */ 'B', 'I', 'N', 'S', 'R', 'I', '_', 'H', 0,
  /* 7490 */ 'S', 'P', 'L', 'A', 'T', 'I', '_', 'H', 0,
  /* 7499 */ 'B', 'S', 'E', 'T', 'I', '_', 'H', 0,
  /* 7507 */ 'S', 'U', 'B', 'V', 'I', '_', 'H', 0,
  /* 7515 */ 'A', 'D', 'D', 'V', 'I', '_', 'H', 0,
  /* 7523 */ 'F', 'I', 'L', 'L', '_', 'H', 0,
  /* 7530 */ 'S', 'L', 'L', '_', 'H', 0,
  /* 7536 */ 'S', 'R', 'L', '_', 'H', 0,
  /* 7542 */ 'B', 'I', 'N', 'S', 'L', '_', 'H', 0,
  /* 7550 */ 'I', 'L', 'V', 'L', '_', 'H', 0,
  /* 7557 */ 'F', 'E', 'X', 'D', 'O', '_', 'H', 0,
  /* 7565 */ 'C', 'E', 'Q', '_', 'H', 0,
  /* 7571 */ 'F', 'T', 'Q', '_', 'H', 0,
  /* 7577 */ 'M', 'S', 'U', 'B', '_', 'Q', '_', 'H', 0,
  /* 7586 */ 'M', 'A', 'D', 'D', '_', 'Q', '_', 'H', 0,
  /* 7595 */ 'M', 'U', 'L', '_', 'Q', '_', 'H', 0,
  /* 7603 */ 'M', 'S', 'U', 'B', 'R', '_', 'Q', '_', 'H', 0,
  /* 7613 */ 'M', 'A', 'D', 'D', 'R', '_', 'Q', '_', 'H', 0,
  /* 7623 */ 'M', 'U', 'L', 'R', '_', 'Q', '_', 'H', 0,
  /* 7632 */ 'S', 'R', 'A', 'R', '_', 'H', 0,
  /* 7639 */ 'B', 'C', 'L', 'R', '_', 'H', 0,
  /* 7646 */ 'S', 'R', 'L', 'R', '_', 'H', 0,
  /* 7653 */ 'B', 'I', 'N', 'S', 'R', '_', 'H', 0,
  /* 7661 */ 'I', 'L', 'V', 'R', '_', 'H', 0,
  /* 7668 */ 'A', 'S', 'U', 'B', '_', 'S', '_', 'H', 0,
  /* 7677 */ 'H', 'S', 'U', 'B', '_', 'S', '_', 'H', 0,
  /* 7686 */ 'D', 'P', 'S', 'U', 'B', '_', 'S', '_', 'H', 0,
  /* 7696 */ 'H', 'A', 'D', 'D', '_', 'S', '_', 'H', 0,
  /* 7705 */ 'D', 'P', 'A', 'D', 'D', '_', 'S', '_', 'H', 0,
  /* 7715 */ 'M', 'O', 'D', '_', 'S', '_', 'H', 0,
  /* 7723 */ 'C', 'L', 'E', '_', 'S', '_', 'H', 0,
  /* 7731 */ 'A', 'V', 'E', '_', 'S', '_', 'H', 0,
  /* 7739 */ 'C', 'L', 'E', 'I', '_', 'S', '_', 'H', 0,
  /* 7748 */ 'M', 'I', 'N', 'I', '_', 'S', '_', 'H', 0,
  /* 7757 */ 'C', 'L', 'T', 'I', '_', 'S', '_', 'H', 0,
  /* 7766 */ 'M', 'A', 'X', 'I', '_', 'S', '_', 'H', 0,
  /* 7775 */ 'M', 'I', 'N', '_', 'S', '_', 'H', 0,
  /* 7783 */ 'D', 'O', 'T', 'P', '_', 'S', '_', 'H', 0,
  /* 7792 */ 'A', 'V', 'E', 'R', '_', 'S', '_', 'H', 0,
  /* 7801 */ 'E', 'X', 'T', 'R', '_', 'S', '_', 'H', 0,
  /* 7810 */ 'S', 'U', 'B', 'S', '_', 'S', '_', 'H', 0,
  /* 7819 */ 'A', 'D', 'D', 'S', '_', 'S', '_', 'H', 0,
  /* 7828 */ 'S', 'A', 'T', '_', 'S', '_', 'H', 0,
  /* 7836 */ 'C', 'L', 'T', '_', 'S', '_', 'H', 0,
  /* 7844 */ 'S', 'U', 'B', 'S', 'U', 'U', '_', 'S', '_', 'H', 0,
  /* 7855 */ 'D', 'I', 'V', '_', 'S', '_', 'H', 0,
  /* 7863 */ 'E', 'X', 'T', 'R', 'V', '_', 'S', '_', 'H', 0,
  /* 7873 */ 'M', 'A', 'X', '_', 'S', '_', 'H', 0,
  /* 7881 */ 'C', 'O', 'P', 'Y', '_', 'S', '_', 'H', 0,
  /* 7890 */ 'S', 'P', 'L', 'A', 'T', '_', 'H', 0,
  /* 7898 */ 'B', 'S', 'E', 'T', '_', 'H', 0,
  /* 7905 */ 'P', 'C', 'N', 'T', '_', 'H', 0,
  /* 7912 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'H', 0,
  /* 7921 */ 'S', 'T', '_', 'H', 0,
  /* 7926 */ 'A', 'S', 'U', 'B', '_', 'U', '_', 'H', 0,
  /* 7935 */ 'H', 'S', 'U', 'B', '_', 'U', '_', 'H', 0,
  /* 7944 */ 'D', 'P', 'S', 'U', 'B', '_', 'U', '_', 'H', 0,
  /* 7954 */ 'H', 'A', 'D', 'D', '_', 'U', '_', 'H', 0,
  /* 7963 */ 'D', 'P', 'A', 'D', 'D', '_', 'U', '_', 'H', 0,
  /* 7973 */ 'M', 'O', 'D', '_', 'U', '_', 'H', 0,
  /* 7981 */ 'C', 'L', 'E', '_', 'U', '_', 'H', 0,
  /* 7989 */ 'A', 'V', 'E', '_', 'U', '_', 'H', 0,
  /* 7997 */ 'C', 'L', 'E', 'I', '_', 'U', '_', 'H', 0,
  /* 8006 */ 'M', 'I', 'N', 'I', '_', 'U', '_', 'H', 0,
  /* 8015 */ 'C', 'L', 'T', 'I', '_', 'U', '_', 'H', 0,
  /* 8024 */ 'M', 'A', 'X', 'I', '_', 'U', '_', 'H', 0,
  /* 8033 */ 'M', 'I', 'N', '_', 'U', '_', 'H', 0,
  /* 8041 */ 'D', 'O', 'T', 'P', '_', 'U', '_', 'H', 0,
  /* 8050 */ 'A', 'V', 'E', 'R', '_', 'U', '_', 'H', 0,
  /* 8059 */ 'S', 'U', 'B', 'S', '_', 'U', '_', 'H', 0,
  /* 8068 */ 'A', 'D', 'D', 'S', '_', 'U', '_', 'H', 0,
  /* 8077 */ 'S', 'U', 'B', 'S', 'U', 'S', '_', 'U', '_', 'H', 0,
  /* 8088 */ 'S', 'A', 'T', '_', 'U', '_', 'H', 0,
  /* 8096 */ 'C', 'L', 'T', '_', 'U', '_', 'H', 0,
  /* 8104 */ 'D', 'I', 'V', '_', 'U', '_', 'H', 0,
  /* 8112 */ 'M', 'A', 'X', '_', 'U', '_', 'H', 0,
  /* 8120 */ 'C', 'O', 'P', 'Y', '_', 'U', '_', 'H', 0,
  /* 8129 */ 'M', 'S', 'U', 'B', 'V', '_', 'H', 0,
  /* 8137 */ 'M', 'A', 'D', 'D', 'V', '_', 'H', 0,
  /* 8145 */ 'P', 'C', 'K', 'E', 'V', '_', 'H', 0,
  /* 8153 */ 'I', 'L', 'V', 'E', 'V', '_', 'H', 0,
  /* 8161 */ 'M', 'U', 'L', 'V', '_', 'H', 0,
  /* 8168 */ 'B', 'Z', '_', 'H', 0,
  /* 8173 */ 'B', 'N', 'Z', '_', 'H', 0,
  /* 8179 */ 'S', 'Y', 'N', 'C', 'I', 0,
  /* 8185 */ 'D', 'I', 0,
  /* 8188 */ 'T', 'G', 'E', 'I', 0,
  /* 8193 */ 'T', 'N', 'E', 'I', 0,
  /* 8198 */ 'D', 'A', 'H', 'I', 0,
  /* 8203 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'F', 'H', 'I', 0,
  /* 8214 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'T', 'L', 'O', 'H', 'I', 0,
  /* 8227 */ 'P', 'H', 'I', 0,
  /* 8231 */ 'M', 'T', 'H', 'I', 0,
  /* 8236 */ 'T', 'E', 'Q', 'I', 0,
  /* 8241 */ 'D', 'A', 'T', 'I', 0,
  /* 8246 */ 'T', 'L', 'T', 'I', 0,
  /* 8251 */ 'D', 'A', 'U', 'I', 0,
  /* 8256 */ 'T', 'L', 'B', 'W', 'I', 0,
  /* 8262 */ 'M', 'O', 'V', 'N', '_', 'I', '6', '4', '_', 'I', 0,
  /* 8273 */ 'M', 'O', 'V', 'Z', '_', 'I', '6', '4', '_', 'I', 0,
  /* 8284 */ 'M', 'O', 'V', 'F', '_', 'I', 0,
  /* 8291 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'F', '_', 'I', 0,
  /* 8310 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'I', 0,
  /* 8319 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'I', 0,
  /* 8328 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', '_', 'I', 0,
  /* 8343 */ 'M', 'O', 'V', 'T', '_', 'I', 0,
  /* 8350 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'T', '_', 'I', 0,
  /* 8369 */ 'J', 0,
  /* 8371 */ 'B', 'R', 'E', 'A', 'K', 0,
  /* 8377 */ 'B', 'A', 'L', 0,
  /* 8381 */ 'J', 'A', 'L', 0,
  /* 8385 */ 'B', 'G', 'E', 'Z', 'A', 'L', 0,
  /* 8392 */ 'B', 'L', 'T', 'Z', 'A', 'L', 0,
  /* 8399 */ 'M', 'U', 'L', 'E', 'U', '_', 'S', '_', 'P', 'H', '_', 'Q', 'B', 'L', 0,
  /* 8414 */ 'P', 'R', 'E', 'C', 'E', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'L', 0,
  /* 8428 */ 'P', 'R', 'E', 'C', 'E', 'Q', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'L', 0,
  /* 8443 */ 'D', 'P', 'A', 'U', '_', 'H', '_', 'Q', 'B', 'L', 0,
  /* 8454 */ 'D', 'P', 'S', 'U', '_', 'H', '_', 'Q', 'B', 'L', 0,
  /* 8465 */ 'L', 'D', 'L', 0,
  /* 8469 */ 'S', 'D', 'L', 0,
  /* 8473 */ 'G', 'C', '_', 'L', 'A', 'B', 'E', 'L', 0,
  /* 8482 */ 'E', 'H', '_', 'L', 'A', 'B', 'E', 'L', 0,
  /* 8491 */ 'B', 'N', 'E', 'L', 0,
  /* 8496 */ 'B', 'C', '1', 'F', 'L', 0,
  /* 8502 */ 'M', 'A', 'Q', '_', 'S', 'A', '_', 'W', '_', 'P', 'H', 'L', 0,
  /* 8515 */ 'P', 'R', 'E', 'C', 'E', 'Q', '_', 'W', '_', 'P', 'H', 'L', 0,
  /* 8528 */ 'M', 'A', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 'L', 0,
  /* 8540 */ 'M', 'U', 'L', 'E', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 'L', 0,
  /* 8554 */ 'T', 'A', 'I', 'L', 'C', 'A', 'L', 'L', 0,
  /* 8563 */ 'S', 'Y', 'S', 'C', 'A', 'L', 'L', 0,
  /* 8571 */ 'B', 'G', 'E', 'Z', 'A', 'L', 'L', 0,
  /* 8579 */ 'B', 'L', 'T', 'Z', 'A', 'L', 'L', 0,
  /* 8587 */ 'K', 'I', 'L', 'L', 0,
  /* 8592 */ 'D', 'S', 'L', 'L', 0,
  /* 8597 */ 'B', 'E', 'Q', 'L', 0,
  /* 8602 */ 'D', 'S', 'R', 'L', 0,
  /* 8607 */ 'B', 'C', '1', 'T', 'L', 0,
  /* 8613 */ 'D', 'M', 'U', 'L', 0,
  /* 8618 */ 'L', 'W', 'L', 0,
  /* 8622 */ 'S', 'W', 'L', 0,
  /* 8626 */ 'B', 'G', 'E', 'Z', 'L', 0,
  /* 8632 */ 'B', 'L', 'E', 'Z', 'L', 0,
  /* 8638 */ 'B', 'G', 'T', 'Z', 'L', 0,
  /* 8644 */ 'B', 'L', 'T', 'Z', 'L', 0,
  /* 8650 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'V', 'T', '_', 'D', '6', '4', '_', 'L', 0,
  /* 8666 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'V', 'T', '_', 'S', '_', 'L', 0,
  /* 8680 */ 'L', 'D', 'C', '1', '_', 'M', 'M', 0,
  /* 8688 */ 'S', 'D', 'C', '1', '_', 'M', 'M', 0,
  /* 8696 */ 'C', 'F', 'C', '1', '_', 'M', 'M', 0,
  /* 8704 */ 'M', 'F', 'C', '1', '_', 'M', 'M', 0,
  /* 8712 */ 'M', 'F', 'H', 'C', '1', '_', 'M', 'M', 0,
  /* 8721 */ 'M', 'T', 'H', 'C', '1', '_', 'M', 'M', 0,
  /* 8730 */ 'C', 'T', 'C', '1', '_', 'M', 'M', 0,
  /* 8738 */ 'M', 'T', 'C', '1', '_', 'M', 'M', 0,
  /* 8746 */ 'L', 'W', 'C', '1', '_', 'M', 'M', 0,
  /* 8754 */ 'S', 'W', 'C', '1', '_', 'M', 'M', 0,
  /* 8762 */ 'L', 'U', 'X', 'C', '1', '_', 'M', 'M', 0,
  /* 8771 */ 'S', 'U', 'X', 'C', '1', '_', 'M', 'M', 0,
  /* 8780 */ 'L', 'W', 'X', 'C', '1', '_', 'M', 'M', 0,
  /* 8789 */ 'S', 'W', 'X', 'C', '1', '_', 'M', 'M', 0,
  /* 8798 */ 'N', 'M', 'S', 'U', 'B', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8811 */ 'N', 'M', 'A', 'D', 'D', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8824 */ 'M', 'O', 'V', 'F', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8836 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8850 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8864 */ 'F', 'C', 'M', 'P', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8876 */ 'C', 'V', 'T', '_', 'S', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8889 */ 'M', 'O', 'V', 'T', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8901 */ 'F', 'M', 'O', 'V', '_', 'D', '3', '2', '_', 'M', 'M', 0,
  /* 8913 */ 'L', 'W', 'M', '3', '2', '_', 'M', 'M', 0,
  /* 8922 */ 'S', 'W', 'M', '3', '2', '_', 'M', 'M', 0,
  /* 8931 */ 'F', 'C', 'M', 'P', '_', 'S', '3', '2', '_', 'M', 'M', 0,
  /* 8943 */ 'A', 'D', 'D', 'I', 'U', 'R', '2', '_', 'M', 'M', 0,
  /* 8954 */ 'C', 'V', 'T', '_', 'L', '_', 'D', '6', '4', '_', 'M', 'M', 0,
  /* 8967 */ 'A', 'D', 'D', 'I', 'U', 'S', '5', '_', 'M', 'M', 0,
  /* 8978 */ 'S', 'B', '1', '6', '_', 'M', 'M', 0,
  /* 8986 */ 'J', 'R', 'C', '1', '6', '_', 'M', 'M', 0,
  /* 8995 */ 'A', 'N', 'D', '1', '6', '_', 'M', 'M', 0,
  /* 9004 */ 'M', 'O', 'V', 'E', '1', '6', '_', 'M', 'M', 0,
  /* 9014 */ 'S', 'H', '1', '6', '_', 'M', 'M', 0,
  /* 9022 */ 'A', 'N', 'D', 'I', '1', '6', '_', 'M', 'M', 0,
  /* 9032 */ 'M', 'F', 'H', 'I', '1', '6', '_', 'M', 'M', 0,
  /* 9042 */ 'L', 'I', '1', '6', '_', 'M', 'M', 0,
  /* 9050 */ 'B', 'R', 'E', 'A', 'K', '1', '6', '_', 'M', 'M', 0,
  /* 9061 */ 'S', 'L', 'L', '1', '6', '_', 'M', 'M', 0,
  /* 9070 */ 'S', 'R', 'L', '1', '6', '_', 'M', 'M', 0,
  /* 9079 */ 'L', 'W', 'M', '1', '6', '_', 'M', 'M', 0,
  /* 9088 */ 'S', 'W', 'M', '1', '6', '_', 'M', 'M', 0,
  /* 9097 */ 'M', 'F', 'L', 'O', '1', '6', '_', 'M', 'M', 0,
  /* 9107 */ 'S', 'D', 'B', 'B', 'P', '1', '6', '_', 'M', 'M', 0,
  /* 9118 */ 'J', 'R', '1', '6', '_', 'M', 'M', 0,
  /* 9126 */ 'J', 'A', 'L', 'R', '1', '6', '_', 'M', 'M', 0,
  /* 9136 */ 'X', 'O', 'R', '1', '6', '_', 'M', 'M', 0,
  /* 9145 */ 'J', 'A', 'L', 'R', 'S', '1', '6', '_', 'M', 'M', 0,
  /* 9156 */ 'N', 'O', 'T', '1', '6', '_', 'M', 'M', 0,
  /* 9165 */ 'L', 'B', 'U', '1', '6', '_', 'M', 'M', 0,
  /* 9174 */ 'S', 'U', 'B', 'U', '1', '6', '_', 'M', 'M', 0,
  /* 9184 */ 'A', 'D', 'D', 'U', '1', '6', '_', 'M', 'M', 0,
  /* 9194 */ 'L', 'H', 'U', '1', '6', '_', 'M', 'M', 0,
  /* 9203 */ 'L', 'W', '1', '6', '_', 'M', 'M', 0,
  /* 9211 */ 'S', 'W', '1', '6', '_', 'M', 'M', 0,
  /* 9219 */ 'B', 'N', 'E', 'Z', '1', '6', '_', 'M', 'M', 0,
  /* 9229 */ 'B', 'E', 'Q', 'Z', '1', '6', '_', 'M', 'M', 0,
  /* 9239 */ 'S', 'R', 'A', '_', 'M', 'M', 0,
  /* 9246 */ 'S', 'E', 'B', '_', 'M', 'M', 0,
  /* 9253 */ 'E', 'H', 'B', '_', 'M', 'M', 0,
  /* 9260 */ 'L', 'B', '_', 'M', 'M', 0,
  /* 9266 */ 'S', 'B', '_', 'M', 'M', 0,
  /* 9272 */ 'F', 'S', 'U', 'B', '_', 'M', 'M', 0,
  /* 9280 */ 'M', 'S', 'U', 'B', '_', 'M', 'M', 0,
  /* 9288 */ 'S', 'Y', 'N', 'C', '_', 'M', 'M', 0,
  /* 9296 */ 'S', 'C', '_', 'M', 'M', 0,
  /* 9302 */ 'B', 'N', 'E', 'Z', 'C', '_', 'M', 'M', 0,
  /* 9311 */ 'B', 'E', 'Q', 'Z', 'C', '_', 'M', 'M', 0,
  /* 9320 */ 'F', 'A', 'D', 'D', '_', 'M', 'M', 0,
  /* 9328 */ 'M', 'A', 'D', 'D', '_', 'M', 'M', 0,
  /* 9336 */ 'A', 'N', 'D', '_', 'M', 'M', 0,
  /* 9343 */ 'T', 'G', 'E', '_', 'M', 'M', 0,
  /* 9350 */ 'C', 'A', 'C', 'H', 'E', '_', 'M', 'M', 0,
  /* 9359 */ 'B', 'N', 'E', '_', 'M', 'M', 0,
  /* 9366 */ 'T', 'N', 'E', '_', 'M', 'M', 0,
  /* 9373 */ 'P', 'A', 'U', 'S', 'E', '_', 'M', 'M', 0,
  /* 9382 */ 'B', 'C', '1', 'F', '_', 'M', 'M', 0,
  /* 9390 */ 'P', 'R', 'E', 'F', '_', 'M', 'M', 0,
  /* 9398 */ 'F', 'N', 'E', 'G', '_', 'M', 'M', 0,
  /* 9406 */ 'W', 'S', 'B', 'H', '_', 'M', 'M', 0,
  /* 9414 */ 'S', 'E', 'H', '_', 'M', 'M', 0,
  /* 9421 */ 'L', 'H', '_', 'M', 'M', 0,
  /* 9427 */ 'S', 'H', '_', 'M', 'M', 0,
  /* 9433 */ 'D', 'I', '_', 'M', 'M', 0,
  /* 9439 */ 'T', 'G', 'E', 'I', '_', 'M', 'M', 0,
  /* 9447 */ 'T', 'N', 'E', 'I', '_', 'M', 'M', 0,
  /* 9455 */ 'M', 'F', 'H', 'I', '_', 'M', 'M', 0,
  /* 9463 */ 'M', 'T', 'H', 'I', '_', 'M', 'M', 0,
  /* 9471 */ 'T', 'E', 'Q', 'I', '_', 'M', 'M', 0,
  /* 9479 */ 'T', 'L', 'T', 'I', '_', 'M', 'M', 0,
  /* 9487 */ 'T', 'L', 'B', 'W', 'I', '_', 'M', 'M', 0,
  /* 9496 */ 'M', 'O', 'V', 'F', '_', 'I', '_', 'M', 'M', 0,
  /* 9506 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'M', 'M', 0,
  /* 9516 */ 'M', 'O', 'V', 'T', '_', 'I', '_', 'M', 'M', 0,
  /* 9526 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'M', 'M', 0,
  /* 9536 */ 'J', '_', 'M', 'M', 0,
  /* 9541 */ 'B', 'R', 'E', 'A', 'K', '_', 'M', 'M', 0,
  /* 9550 */ 'J', 'A', 'L', '_', 'M', 'M', 0,
  /* 9557 */ 'B', 'G', 'E', 'Z', 'A', 'L', '_', 'M', 'M', 0,
  /* 9567 */ 'B', 'L', 'T', 'Z', 'A', 'L', '_', 'M', 'M', 0,
  /* 9577 */ 'S', 'Y', 'S', 'C', 'A', 'L', 'L', '_', 'M', 'M', 0,
  /* 9588 */ 'S', 'L', 'L', '_', 'M', 'M', 0,
  /* 9595 */ 'S', 'R', 'L', '_', 'M', 'M', 0,
  /* 9602 */ 'F', 'M', 'U', 'L', '_', 'M', 'M', 0,
  /* 9610 */ 'L', 'W', 'L', '_', 'M', 'M', 0,
  /* 9617 */ 'S', 'W', 'L', '_', 'M', 'M', 0,
  /* 9624 */ 'C', 'L', 'O', '_', 'M', 'M', 0,
  /* 9631 */ 'M', 'F', 'L', 'O', '_', 'M', 'M', 0,
  /* 9639 */ 'M', 'T', 'L', 'O', '_', 'M', 'M', 0,
  /* 9647 */ 'S', 'D', 'B', 'B', 'P', '_', 'M', 'M', 0,
  /* 9656 */ 'T', 'L', 'B', 'P', '_', 'M', 'M', 0,
  /* 9664 */ 'S', 'S', 'N', 'O', 'P', '_', 'M', 'M', 0,
  /* 9673 */ 'A', 'D', 'D', 'I', 'U', 'R', '1', 'S', 'P', '_', 'M', 'M', 0,
  /* 9686 */ 'A', 'D', 'D', 'I', 'U', 'S', 'P', '_', 'M', 'M', 0,
  /* 9697 */ 'L', 'W', 'S', 'P', '_', 'M', 'M', 0,
  /* 9705 */ 'S', 'W', 'S', 'P', '_', 'M', 'M', 0,
  /* 9713 */ 'L', 'W', 'P', '_', 'M', 'M', 0,
  /* 9720 */ 'S', 'W', 'P', '_', 'M', 'M', 0,
  /* 9727 */ 'B', 'E', 'Q', '_', 'M', 'M', 0,
  /* 9734 */ 'T', 'E', 'Q', '_', 'M', 'M', 0,
  /* 9741 */ 'T', 'L', 'B', 'R', '_', 'M', 'M', 0,
  /* 9749 */ 'J', 'R', '_', 'M', 'M', 0,
  /* 9755 */ 'J', 'A', 'L', 'R', '_', 'M', 'M', 0,
  /* 9763 */ 'N', 'O', 'R', '_', 'M', 'M', 0,
  /* 9770 */ 'X', 'O', 'R', '_', 'M', 'M', 0,
  /* 9777 */ 'R', 'O', 'T', 'R', '_', 'M', 'M', 0,
  /* 9785 */ 'T', 'L', 'B', 'W', 'R', '_', 'M', 'M', 0,
  /* 9794 */ 'R', 'D', 'H', 'W', 'R', '_', 'M', 'M', 0,
  /* 9803 */ 'L', 'W', 'R', '_', 'M', 'M', 0,
  /* 9810 */ 'S', 'W', 'R', '_', 'M', 'M', 0,
  /* 9817 */ 'F', 'A', 'B', 'S', '_', 'M', 'M', 0,
  /* 9825 */ 'J', 'A', 'L', 'S', '_', 'M', 'M', 0,
  /* 9833 */ 'B', 'G', 'E', 'Z', 'A', 'L', 'S', '_', 'M', 'M', 0,
  /* 9844 */ 'B', 'L', 'T', 'Z', 'A', 'L', 'S', '_', 'M', 'M', 0,
  /* 9855 */ 'I', 'N', 'S', '_', 'M', 'M', 0,
  /* 9862 */ 'J', 'A', 'L', 'R', 'S', '_', 'M', 'M', 0,
  /* 9871 */ 'L', 'W', 'X', 'S', '_', 'M', 'M', 0,
  /* 9879 */ 'F', 'S', 'U', 'B', '_', 'S', '_', 'M', 'M', 0,
  /* 9889 */ 'N', 'M', 'S', 'U', 'B', '_', 'S', '_', 'M', 'M', 0,
  /* 9900 */ 'F', 'A', 'D', 'D', '_', 'S', '_', 'M', 'M', 0,
  /* 9910 */ 'N', 'M', 'A', 'D', 'D', '_', 'S', '_', 'M', 'M', 0,
  /* 9921 */ 'C', 'V', 'T', '_', 'D', '_', 'S', '_', 'M', 'M', 0,
  /* 9932 */ 'M', 'O', 'V', 'F', '_', 'S', '_', 'M', 'M', 0,
  /* 9942 */ 'F', 'N', 'E', 'G', '_', 'S', '_', 'M', 'M', 0,
  /* 9952 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'S', '_', 'M', 'M', 0,
  /* 9964 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'S', '_', 'M', 'M', 0,
  /* 9976 */ 'F', 'M', 'U', 'L', '_', 'S', '_', 'M', 'M', 0,
  /* 9986 */ 'C', 'V', 'T', '_', 'L', '_', 'S', '_', 'M', 'M', 0,
  /* 9997 */ 'F', 'A', 'B', 'S', '_', 'S', '_', 'M', 'M', 0,
  /* 10007 */ 'F', 'S', 'Q', 'R', 'T', '_', 'S', '_', 'M', 'M', 0,
  /* 10018 */ 'M', 'O', 'V', 'T', '_', 'S', '_', 'M', 'M', 0,
  /* 10028 */ 'F', 'D', 'I', 'V', '_', 'S', '_', 'M', 'M', 0,
  /* 10038 */ 'F', 'M', 'O', 'V', '_', 'S', '_', 'M', 'M', 0,
  /* 10048 */ 'T', 'R', 'U', 'N', 'C', '_', 'W', '_', 'S', '_', 'M', 'M', 0,
  /* 10061 */ 'R', 'O', 'U', 'N', 'D', '_', 'W', '_', 'S', '_', 'M', 'M', 0,
  /* 10074 */ 'C', 'E', 'I', 'L', '_', 'W', '_', 'S', '_', 'M', 'M', 0,
  /* 10086 */ 'F', 'L', 'O', 'O', 'R', '_', 'W', '_', 'S', '_', 'M', 'M', 0,
  /* 10099 */ 'C', 'V', 'T', '_', 'W', '_', 'S', '_', 'M', 'M', 0,
  /* 10110 */ 'B', 'C', '1', 'T', '_', 'M', 'M', 0,
  /* 10118 */ 'D', 'E', 'R', 'E', 'T', '_', 'M', 'M', 0,
  /* 10127 */ 'W', 'A', 'I', 'T', '_', 'M', 'M', 0,
  /* 10135 */ 'S', 'L', 'T', '_', 'M', 'M', 0,
  /* 10142 */ 'T', 'L', 'T', '_', 'M', 'M', 0,
  /* 10149 */ 'M', 'U', 'L', 'T', '_', 'M', 'M', 0,
  /* 10157 */ 'F', 'S', 'Q', 'R', 'T', '_', 'M', 'M', 0,
  /* 10166 */ 'E', 'X', 'T', '_', 'M', 'M', 0,
  /* 10173 */ 'M', 'S', 'U', 'B', 'U', '_', 'M', 'M', 0,
  /* 10182 */ 'M', 'A', 'D', 'D', 'U', '_', 'M', 'M', 0,
  /* 10191 */ 'T', 'G', 'E', 'U', '_', 'M', 'M', 0,
  /* 10199 */ 'T', 'G', 'E', 'I', 'U', '_', 'M', 'M', 0,
  /* 10208 */ 'T', 'L', 'T', 'I', 'U', '_', 'M', 'M', 0,
  /* 10217 */ 'T', 'L', 'T', 'U', '_', 'M', 'M', 0,
  /* 10225 */ 'L', 'W', 'U', '_', 'M', 'M', 0,
  /* 10232 */ 'S', 'R', 'A', 'V', '_', 'M', 'M', 0,
  /* 10240 */ 'F', 'D', 'I', 'V', '_', 'M', 'M', 0,
  /* 10248 */ 'S', 'D', 'I', 'V', '_', 'M', 'M', 0,
  /* 10256 */ 'U', 'D', 'I', 'V', '_', 'M', 'M', 0,
  /* 10264 */ 'S', 'L', 'L', 'V', '_', 'M', 'M', 0,
  /* 10272 */ 'S', 'R', 'L', 'V', '_', 'M', 'M', 0,
  /* 10280 */ 'R', 'O', 'T', 'R', 'V', '_', 'M', 'M', 0,
  /* 10289 */ 'L', 'W', '_', 'M', 'M', 0,
  /* 10295 */ 'S', 'W', '_', 'M', 'M', 0,
  /* 10301 */ 'C', 'V', 'T', '_', 'D', '3', '2', '_', 'W', '_', 'M', 'M', 0,
  /* 10314 */ 'T', 'R', 'U', 'N', 'C', '_', 'W', '_', 'M', 'M', 0,
  /* 10325 */ 'R', 'O', 'U', 'N', 'D', '_', 'W', '_', 'M', 'M', 0,
  /* 10336 */ 'C', 'E', 'I', 'L', '_', 'W', '_', 'M', 'M', 0,
  /* 10346 */ 'F', 'L', 'O', 'O', 'R', '_', 'W', '_', 'M', 'M', 0,
  /* 10357 */ 'C', 'V', 'T', '_', 'S', '_', 'W', '_', 'M', 'M', 0,
  /* 10368 */ 'C', 'V', 'T', '_', 'W', '_', 'M', 'M', 0,
  /* 10377 */ 'B', 'G', 'E', 'Z', '_', 'M', 'M', 0,
  /* 10385 */ 'B', 'L', 'E', 'Z', '_', 'M', 'M', 0,
  /* 10393 */ 'C', 'L', 'Z', '_', 'M', 'M', 0,
  /* 10400 */ 'B', 'G', 'T', 'Z', '_', 'M', 'M', 0,
  /* 10408 */ 'B', 'L', 'T', 'Z', '_', 'M', 'M', 0,
  /* 10416 */ 'A', 'D', 'D', 'i', '_', 'M', 'M', 0,
  /* 10424 */ 'A', 'N', 'D', 'i', '_', 'M', 'M', 0,
  /* 10432 */ 'X', 'O', 'R', 'i', '_', 'M', 'M', 0,
  /* 10440 */ 'S', 'L', 'T', 'i', '_', 'M', 'M', 0,
  /* 10448 */ 'L', 'U', 'i', '_', 'M', 'M', 0,
  /* 10455 */ 'L', 'B', 'u', '_', 'M', 'M', 0,
  /* 10462 */ 'S', 'U', 'B', 'u', '_', 'M', 'M', 0,
  /* 10470 */ 'A', 'D', 'D', 'u', '_', 'M', 'M', 0,
  /* 10478 */ 'L', 'H', 'u', '_', 'M', 'M', 0,
  /* 10485 */ 'S', 'L', 'T', 'u', '_', 'M', 'M', 0,
  /* 10493 */ 'M', 'U', 'L', 'T', 'u', '_', 'M', 'M', 0,
  /* 10502 */ 'L', 'E', 'A', '_', 'A', 'D', 'D', 'i', 'u', '_', 'M', 'M', 0,
  /* 10515 */ 'S', 'L', 'T', 'i', 'u', '_', 'M', 'M', 0,
  /* 10524 */ 'I', 'N', 'L', 'I', 'N', 'E', 'A', 'S', 'M', 0,
  /* 10534 */ 'D', 'I', 'N', 'S', 'M', 0,
  /* 10540 */ 'D', 'E', 'X', 'T', 'M', 0,
  /* 10546 */ 'B', 'A', 'L', 'I', 'G', 'N', 0,
  /* 10553 */ 'D', 'A', 'L', 'I', 'G', 'N', 0,
  /* 10560 */ 'C', 'F', 'I', '_', 'I', 'N', 'S', 'T', 'R', 'U', 'C', 'T', 'I', 'O', 'N', 0,
  /* 10576 */ 'A', 'D', 'J', 'C', 'A', 'L', 'L', 'S', 'T', 'A', 'C', 'K', 'D', 'O', 'W', 'N', 0,
  /* 10593 */ 'F', 'E', 'X', 'P', '2', '_', 'D', '_', '1', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10610 */ 'F', 'E', 'X', 'P', '2', '_', 'W', '_', '1', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10627 */ 'B', 'P', 'O', 'S', 'G', 'E', '3', '2', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10643 */ 'S', 'N', 'Z', '_', 'B', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10656 */ 'S', 'Z', '_', 'B', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10668 */ 'B', 'S', 'E', 'L', '_', 'F', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10683 */ 'F', 'I', 'L', 'L', '_', 'F', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10698 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'F', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10715 */ 'C', 'O', 'P', 'Y', '_', 'F', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10730 */ 'B', 'S', 'E', 'L', '_', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10744 */ 'A', 'N', 'D', '_', 'V', '_', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10759 */ 'N', 'O', 'R', '_', 'V', '_', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10774 */ 'X', 'O', 'R', '_', 'V', '_', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10789 */ 'S', 'N', 'Z', '_', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10802 */ 'S', 'Z', '_', 'D', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10814 */ 'B', 'S', 'E', 'L', '_', 'H', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10828 */ 'A', 'N', 'D', '_', 'V', '_', 'H', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10843 */ 'N', 'O', 'R', '_', 'V', '_', 'H', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10858 */ 'X', 'O', 'R', '_', 'V', '_', 'H', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10873 */ 'S', 'N', 'Z', '_', 'H', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10886 */ 'S', 'Z', '_', 'H', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10898 */ 'S', 'N', 'Z', '_', 'V', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10911 */ 'S', 'Z', '_', 'V', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10923 */ 'B', 'S', 'E', 'L', '_', 'F', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10938 */ 'F', 'I', 'L', 'L', '_', 'F', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10953 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'F', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10970 */ 'C', 'O', 'P', 'Y', '_', 'F', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10985 */ 'B', 'S', 'E', 'L', '_', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 10999 */ 'A', 'N', 'D', '_', 'V', '_', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11014 */ 'N', 'O', 'R', '_', 'V', '_', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11029 */ 'X', 'O', 'R', '_', 'V', '_', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11044 */ 'S', 'N', 'Z', '_', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11057 */ 'S', 'Z', '_', 'W', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11069 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'B', '_', 'V', 'I', 'D', 'X', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11090 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'F', 'D', '_', 'V', 'I', 'D', 'X', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11112 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'D', '_', 'V', 'I', 'D', 'X', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11133 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'H', '_', 'V', 'I', 'D', 'X', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11154 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'F', 'W', '_', 'V', 'I', 'D', 'X', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11176 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'W', '_', 'V', 'I', 'D', 'X', '_', 'P', 'S', 'E', 'U', 'D', 'O', 0,
  /* 11197 */ 'D', 'C', 'L', 'O', 0,
  /* 11202 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'F', 'L', 'O', 0,
  /* 11213 */ 'S', 'H', 'I', 'L', 'O', 0,
  /* 11219 */ 'M', 'T', 'L', 'O', 0,
  /* 11224 */ 'S', 'T', 'A', 'C', 'K', 'M', 'A', 'P', 0,
  /* 11233 */ 'T', 'R', 'A', 'P', 0,
  /* 11238 */ 'D', 'B', 'I', 'T', 'S', 'W', 'A', 'P', 0,
  /* 11247 */ 'S', 'D', 'B', 'B', 'P', 0,
  /* 11253 */ 'T', 'L', 'B', 'P', 0,
  /* 11258 */ 'E', 'X', 'T', 'P', 'D', 'P', 0,
  /* 11265 */ 'M', 'T', 'H', 'L', 'I', 'P', 0,
  /* 11272 */ 'S', 'S', 'N', 'O', 'P', 0,
  /* 11278 */ 'D', 'P', 'O', 'P', 0,
  /* 11283 */ 'L', 'O', 'A', 'D', '_', 'A', 'C', 'C', '6', '4', 'D', 'S', 'P', 0,
  /* 11297 */ 'S', 'T', 'O', 'R', 'E', '_', 'A', 'C', 'C', '6', '4', 'D', 'S', 'P', 0,
  /* 11312 */ 'R', 'D', 'D', 'S', 'P', 0,
  /* 11318 */ 'W', 'R', 'D', 'S', 'P', 0,
  /* 11324 */ 'M', 'S', 'U', 'B', '_', 'D', 'S', 'P', 0,
  /* 11333 */ 'M', 'A', 'D', 'D', '_', 'D', 'S', 'P', 0,
  /* 11342 */ 'L', 'O', 'A', 'D', '_', 'C', 'C', 'O', 'N', 'D', '_', 'D', 'S', 'P', 0,
  /* 11357 */ 'S', 'T', 'O', 'R', 'E', '_', 'C', 'C', 'O', 'N', 'D', '_', 'D', 'S', 'P', 0,
  /* 11373 */ 'M', 'F', 'H', 'I', '_', 'D', 'S', 'P', 0,
  /* 11382 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'T', 'L', 'O', 'H', 'I', '_', 'D', 'S', 'P', 0,
  /* 11399 */ 'M', 'T', 'H', 'I', '_', 'D', 'S', 'P', 0,
  /* 11408 */ 'M', 'F', 'L', 'O', '_', 'D', 'S', 'P', 0,
  /* 11417 */ 'M', 'T', 'L', 'O', '_', 'D', 'S', 'P', 0,
  /* 11426 */ 'M', 'U', 'L', 'T', '_', 'D', 'S', 'P', 0,
  /* 11435 */ 'M', 'S', 'U', 'B', 'U', '_', 'D', 'S', 'P', 0,
  /* 11445 */ 'M', 'A', 'D', 'D', 'U', '_', 'D', 'S', 'P', 0,
  /* 11455 */ 'M', 'U', 'L', 'T', 'U', '_', 'D', 'S', 'P', 0,
  /* 11465 */ 'J', 'R', 'A', 'D', 'D', 'I', 'U', 'S', 'P', 0,
  /* 11475 */ 'E', 'X', 'T', 'P', 0,
  /* 11480 */ 'A', 'D', 'J', 'C', 'A', 'L', 'L', 'S', 'T', 'A', 'C', 'K', 'U', 'P', 0,
  /* 11495 */ 'B', 'E', 'Q', 0,
  /* 11499 */ 'S', 'E', 'Q', 0,
  /* 11503 */ 'T', 'E', 'Q', 0,
  /* 11507 */ 'T', 'L', 'B', 'R', 0,
  /* 11512 */ 'M', 'U', 'L', 'E', 'U', '_', 'S', '_', 'P', 'H', '_', 'Q', 'B', 'R', 0,
  /* 11527 */ 'P', 'R', 'E', 'C', 'E', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'R', 0,
  /* 11541 */ 'P', 'R', 'E', 'C', 'E', 'Q', 'U', '_', 'P', 'H', '_', 'Q', 'B', 'R', 0,
  /* 11556 */ 'D', 'P', 'A', 'U', '_', 'H', '_', 'Q', 'B', 'R', 0,
  /* 11567 */ 'D', 'P', 'S', 'U', '_', 'H', '_', 'Q', 'B', 'R', 0,
  /* 11578 */ 'B', 'A', 'L', '_', 'B', 'R', 0,
  /* 11585 */ 'L', 'D', 'R', 0,
  /* 11589 */ 'S', 'D', 'R', 0,
  /* 11593 */ 'M', 'A', 'Q', '_', 'S', 'A', '_', 'W', '_', 'P', 'H', 'R', 0,
  /* 11606 */ 'P', 'R', 'E', 'C', 'E', 'Q', '_', 'W', '_', 'P', 'H', 'R', 0,
  /* 11619 */ 'M', 'A', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 'R', 0,
  /* 11631 */ 'M', 'U', 'L', 'E', 'Q', '_', 'S', '_', 'W', '_', 'P', 'H', 'R', 0,
  /* 11645 */ 'J', 'R', 0,
  /* 11648 */ 'J', 'A', 'L', 'R', 0,
  /* 11653 */ 'N', 'O', 'R', 0,
  /* 11657 */ 'X', 'O', 'R', 0,
  /* 11661 */ 'D', 'R', 'O', 'T', 'R', 0,
  /* 11667 */ 'T', 'L', 'B', 'W', 'R', 0,
  /* 11673 */ 'R', 'D', 'H', 'W', 'R', 0,
  /* 11679 */ 'L', 'W', 'R', 0,
  /* 11683 */ 'S', 'W', 'R', 0,
  /* 11687 */ 'T', 'A', 'I', 'L', 'C', 'A', 'L', 'L', '6', '4', '_', 'R', 0,
  /* 11700 */ 'T', 'A', 'I', 'L', 'C', 'A', 'L', 'L', '_', 'R', 0,
  /* 11711 */ 'C', 'I', 'N', 'S', 0,
  /* 11716 */ 'D', 'I', 'N', 'S', 0,
  /* 11721 */ 'C', 'O', 'P', 'Y', '_', 'T', 'O', '_', 'R', 'E', 'G', 'C', 'L', 'A', 'S', 'S', 0,
  /* 11738 */ 'E', 'X', 'T', 'S', 0,
  /* 11743 */ 'C', 'V', 'T', '_', 'D', '3', '2', '_', 'S', 0,
  /* 11753 */ 'C', 'V', 'T', '_', 'D', '6', '4', '_', 'S', 0,
  /* 11763 */ 'M', 'O', 'V', 'N', '_', 'I', '6', '4', '_', 'S', 0,
  /* 11774 */ 'M', 'O', 'V', 'Z', '_', 'I', '6', '4', '_', 'S', 0,
  /* 11785 */ 'M', 'I', 'N', 'A', '_', 'S', 0,
  /* 11792 */ 'M', 'A', 'X', 'A', '_', 'S', 0,
  /* 11799 */ 'F', 'S', 'U', 'B', '_', 'S', 0,
  /* 11806 */ 'N', 'M', 'S', 'U', 'B', '_', 'S', 0,
  /* 11814 */ 'F', 'A', 'D', 'D', '_', 'S', 0,
  /* 11821 */ 'N', 'M', 'A', 'D', 'D', '_', 'S', 0,
  /* 11829 */ 'C', '_', 'N', 'G', 'E', '_', 'S', 0,
  /* 11837 */ 'C', '_', 'N', 'G', 'L', 'E', '_', 'S', 0,
  /* 11846 */ 'C', '_', 'O', 'L', 'E', '_', 'S', 0,
  /* 11854 */ 'C', 'M', 'P', '_', 'S', 'L', 'E', '_', 'S', 0,
  /* 11864 */ 'C', 'M', 'P', '_', 'S', 'U', 'L', 'E', '_', 'S', 0,
  /* 11875 */ 'C', '_', 'U', 'L', 'E', '_', 'S', 0,
  /* 11883 */ 'C', 'M', 'P', '_', 'U', 'L', 'E', '_', 'S', 0,
  /* 11893 */ 'C', '_', 'L', 'E', '_', 'S', 0,
  /* 11900 */ 'C', 'M', 'P', '_', 'L', 'E', '_', 'S', 0,
  /* 11909 */ 'C', 'M', 'P', '_', 'S', 'A', 'F', '_', 'S', 0,
  /* 11919 */ 'M', 'S', 'U', 'B', 'F', '_', 'S', 0,
  /* 11927 */ 'M', 'A', 'D', 'D', 'F', '_', 'S', 0,
  /* 11935 */ 'C', '_', 'S', 'F', '_', 'S', 0,
  /* 11942 */ 'M', 'O', 'V', 'F', '_', 'S', 0,
  /* 11949 */ 'C', '_', 'F', '_', 'S', 0,
  /* 11955 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'F', '_', 'S', 0,
  /* 11974 */ 'C', 'M', 'P', '_', 'F', '_', 'S', 0,
  /* 11982 */ 'F', 'N', 'E', 'G', '_', 'S', 0,
  /* 11989 */ 'M', 'O', 'V', 'N', '_', 'I', '_', 'S', 0,
  /* 11998 */ 'M', 'O', 'V', 'Z', '_', 'I', '_', 'S', 0,
  /* 12007 */ 'S', 'E', 'L', '_', 'S', 0,
  /* 12013 */ 'C', '_', 'N', 'G', 'L', '_', 'S', 0,
  /* 12021 */ 'F', 'M', 'U', 'L', '_', 'S', 0,
  /* 12028 */ 'T', 'R', 'U', 'N', 'C', '_', 'L', '_', 'S', 0,
  /* 12038 */ 'R', 'O', 'U', 'N', 'D', '_', 'L', '_', 'S', 0,
  /* 12048 */ 'C', 'E', 'I', 'L', '_', 'L', '_', 'S', 0,
  /* 12057 */ 'F', 'L', 'O', 'O', 'R', '_', 'L', '_', 'S', 0,
  /* 12067 */ 'C', 'V', 'T', '_', 'L', '_', 'S', 0,
  /* 12075 */ 'M', 'I', 'N', '_', 'S', 0,
  /* 12081 */ 'C', 'M', 'P', '_', 'S', 'U', 'N', '_', 'S', 0,
  /* 12091 */ 'C', '_', 'U', 'N', '_', 'S', 0,
  /* 12098 */ 'C', 'M', 'P', '_', 'U', 'N', '_', 'S', 0,
  /* 12107 */ 'C', '_', 'S', 'E', 'Q', '_', 'S', 0,
  /* 12115 */ 'C', 'M', 'P', '_', 'S', 'E', 'Q', '_', 'S', 0,
  /* 12125 */ 'C', 'M', 'P', '_', 'S', 'U', 'E', 'Q', '_', 'S', 0,
  /* 12136 */ 'C', '_', 'U', 'E', 'Q', '_', 'S', 0,
  /* 12144 */ 'C', 'M', 'P', '_', 'U', 'E', 'Q', '_', 'S', 0,
  /* 12154 */ 'C', '_', 'E', 'Q', '_', 'S', 0,
  /* 12161 */ 'C', 'M', 'P', '_', 'E', 'Q', '_', 'S', 0,
  /* 12170 */ 'F', 'A', 'B', 'S', '_', 'S', 0,
  /* 12177 */ 'C', 'L', 'A', 'S', 'S', '_', 'S', 0,
  /* 12185 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', '_', 'S', 0,
  /* 12200 */ 'C', '_', 'N', 'G', 'T', '_', 'S', 0,
  /* 12208 */ 'C', '_', 'O', 'L', 'T', '_', 'S', 0,
  /* 12216 */ 'C', 'M', 'P', '_', 'S', 'L', 'T', '_', 'S', 0,
  /* 12226 */ 'C', 'M', 'P', '_', 'S', 'U', 'L', 'T', '_', 'S', 0,
  /* 12237 */ 'C', '_', 'U', 'L', 'T', '_', 'S', 0,
  /* 12245 */ 'C', 'M', 'P', '_', 'U', 'L', 'T', '_', 'S', 0,
  /* 12255 */ 'C', '_', 'L', 'T', '_', 'S', 0,
  /* 12262 */ 'C', 'M', 'P', '_', 'L', 'T', '_', 'S', 0,
  /* 12271 */ 'R', 'I', 'N', 'T', '_', 'S', 0,
  /* 12278 */ 'F', 'S', 'Q', 'R', 'T', '_', 'S', 0,
  /* 12286 */ 'M', 'O', 'V', 'T', '_', 'S', 0,
  /* 12293 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'E', 'L', 'E', 'C', 'T', 'F', 'P', '_', 'T', '_', 'S', 0,
  /* 12312 */ 'F', 'D', 'I', 'V', '_', 'S', 0,
  /* 12319 */ 'F', 'M', 'O', 'V', '_', 'S', 0,
  /* 12326 */ 'T', 'R', 'U', 'N', 'C', '_', 'W', '_', 'S', 0,
  /* 12336 */ 'R', 'O', 'U', 'N', 'D', '_', 'W', '_', 'S', 0,
  /* 12346 */ 'C', 'E', 'I', 'L', '_', 'W', '_', 'S', 0,
  /* 12355 */ 'F', 'L', 'O', 'O', 'R', '_', 'W', '_', 'S', 0,
  /* 12365 */ 'C', 'V', 'T', '_', 'W', '_', 'S', 0,
  /* 12373 */ 'M', 'A', 'X', '_', 'S', 0,
  /* 12379 */ 'S', 'E', 'L', 'N', 'E', 'Z', '_', 'S', 0,
  /* 12388 */ 'S', 'E', 'L', 'E', 'Q', 'Z', '_', 'S', 0,
  /* 12397 */ 'B', 'C', '1', 'T', 0,
  /* 12402 */ 'D', 'E', 'R', 'E', 'T', 0,
  /* 12408 */ 'W', 'A', 'I', 'T', 0,
  /* 12413 */ 'S', 'L', 'T', 0,
  /* 12417 */ 'T', 'L', 'T', 0,
  /* 12421 */ 'P', 's', 'e', 'u', 'd', 'o', 'D', 'M', 'U', 'L', 'T', 0,
  /* 12433 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'U', 'L', 'T', 0,
  /* 12444 */ 'S', 'T', 'A', 'T', 'E', 'P', 'O', 'I', 'N', 'T', 0,
  /* 12455 */ 'P', 'A', 'T', 'C', 'H', 'P', 'O', 'I', 'N', 'T', 0,
  /* 12466 */ 'L', 'I', 'F', 'E', 'T', 'I', 'M', 'E', '_', 'S', 'T', 'A', 'R', 'T', 0,
  /* 12481 */ 'D', 'E', 'X', 'T', 0,
  /* 12486 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'S', 'U', 'B', 'U', 0,
  /* 12498 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'A', 'D', 'D', 'U', 0,
  /* 12510 */ 'D', 'M', 'O', 'D', 'U', 0,
  /* 12516 */ 'T', 'G', 'E', 'U', 0,
  /* 12521 */ 'D', 'M', 'U', 'H', 'U', 0,
  /* 12527 */ 'T', 'G', 'E', 'I', 'U', 0,
  /* 12533 */ 'T', 'T', 'L', 'T', 'I', 'U', 0,
  /* 12540 */ 'V', '3', 'M', 'U', 'L', 'U', 0,
  /* 12547 */ 'D', 'M', 'U', 'L', 'U', 0,
  /* 12553 */ 'V', 'M', 'U', 'L', 'U', 0,
  /* 12559 */ 'D', 'I', 'N', 'S', 'U', 0,
  /* 12565 */ 'T', 'L', 'T', 'U', 0,
  /* 12570 */ 'D', 'E', 'X', 'T', 'U', 0,
  /* 12576 */ 'D', 'D', 'I', 'V', 'U', 0,
  /* 12582 */ 'D', 'S', 'R', 'A', 'V', 0,
  /* 12588 */ 'B', 'I', 'T', 'R', 'E', 'V', 0,
  /* 12595 */ 'D', 'D', 'I', 'V', 0,
  /* 12600 */ 'P', 's', 'e', 'u', 'd', 'o', 'D', 'S', 'D', 'I', 'V', 0,
  /* 12612 */ 'P', 's', 'e', 'u', 'd', 'o', 'S', 'D', 'I', 'V', 0,
  /* 12623 */ 'P', 's', 'e', 'u', 'd', 'o', 'D', 'U', 'D', 'I', 'V', 0,
  /* 12635 */ 'P', 's', 'e', 'u', 'd', 'o', 'U', 'D', 'I', 'V', 0,
  /* 12646 */ 'D', 'S', 'L', 'L', 'V', 0,
  /* 12652 */ 'D', 'S', 'R', 'L', 'V', 0,
  /* 12658 */ 'S', 'H', 'I', 'L', 'O', 'V', 0,
  /* 12665 */ 'E', 'X', 'T', 'P', 'D', 'P', 'V', 0,
  /* 12673 */ 'E', 'X', 'T', 'P', 'V', 0,
  /* 12679 */ 'D', 'R', 'O', 'T', 'R', 'V', 0,
  /* 12686 */ 'I', 'N', 'S', 'V', 0,
  /* 12691 */ 'A', 'N', 'D', '_', 'V', 0,
  /* 12697 */ 'M', 'O', 'V', 'E', '_', 'V', 0,
  /* 12704 */ 'B', 'S', 'E', 'L', '_', 'V', 0,
  /* 12711 */ 'N', 'O', 'R', '_', 'V', 0,
  /* 12717 */ 'X', 'O', 'R', '_', 'V', 0,
  /* 12723 */ 'B', 'Z', '_', 'V', 0,
  /* 12728 */ 'B', 'M', 'Z', '_', 'V', 0,
  /* 12734 */ 'B', 'N', 'Z', '_', 'V', 0,
  /* 12740 */ 'B', 'M', 'N', 'Z', '_', 'V', 0,
  /* 12747 */ 'L', 'W', 0,
  /* 12750 */ 'S', 'W', 0,
  /* 12753 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'V', 'T', '_', 'D', '3', '2', '_', 'W', 0,
  /* 12769 */ 'F', 'L', 'O', 'G', '2', '_', 'W', 0,
  /* 12777 */ 'F', 'E', 'X', 'P', '2', '_', 'W', 0,
  /* 12785 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'V', 'T', '_', 'D', '6', '4', '_', 'W', 0,
  /* 12801 */ 'S', 'R', 'A', '_', 'W', 0,
  /* 12807 */ 'A', 'D', 'D', '_', 'A', '_', 'W', 0,
  /* 12815 */ 'F', 'M', 'I', 'N', '_', 'A', '_', 'W', 0,
  /* 12824 */ 'A', 'D', 'D', 'S', '_', 'A', '_', 'W', 0,
  /* 12833 */ 'F', 'M', 'A', 'X', '_', 'A', '_', 'W', 0,
  /* 12842 */ 'F', 'S', 'U', 'B', '_', 'W', 0,
  /* 12849 */ 'F', 'M', 'S', 'U', 'B', '_', 'W', 0,
  /* 12857 */ 'N', 'L', 'O', 'C', '_', 'W', 0,
  /* 12864 */ 'N', 'L', 'Z', 'C', '_', 'W', 0,
  /* 12871 */ 'F', 'A', 'D', 'D', '_', 'W', 0,
  /* 12878 */ 'F', 'M', 'A', 'D', 'D', '_', 'W', 0,
  /* 12886 */ 'S', 'L', 'D', '_', 'W', 0,
  /* 12892 */ 'P', 'C', 'K', 'O', 'D', '_', 'W', 0,
  /* 12900 */ 'I', 'L', 'V', 'O', 'D', '_', 'W', 0,
  /* 12908 */ 'F', 'C', 'L', 'E', '_', 'W', 0,
  /* 12915 */ 'F', 'S', 'L', 'E', '_', 'W', 0,
  /* 12922 */ 'F', 'C', 'U', 'L', 'E', '_', 'W', 0,
  /* 12930 */ 'F', 'S', 'U', 'L', 'E', '_', 'W', 0,
  /* 12938 */ 'F', 'C', 'N', 'E', '_', 'W', 0,
  /* 12945 */ 'F', 'S', 'N', 'E', '_', 'W', 0,
  /* 12952 */ 'F', 'C', 'U', 'N', 'E', '_', 'W', 0,
  /* 12960 */ 'F', 'S', 'U', 'N', 'E', '_', 'W', 0,
  /* 12968 */ 'I', 'N', 'S', 'V', 'E', '_', 'W', 0,
  /* 12976 */ 'F', 'C', 'A', 'F', '_', 'W', 0,
  /* 12983 */ 'F', 'S', 'A', 'F', '_', 'W', 0,
  /* 12990 */ 'V', 'S', 'H', 'F', '_', 'W', 0,
  /* 12997 */ 'B', 'N', 'E', 'G', '_', 'W', 0,
  /* 13004 */ 'P', 'R', 'E', 'C', 'R', '_', 'S', 'R', 'A', '_', 'P', 'H', '_', 'W', 0,
  /* 13019 */ 'P', 'R', 'E', 'C', 'R', 'Q', '_', 'P', 'H', '_', 'W', 0,
  /* 13031 */ 'P', 'R', 'E', 'C', 'R', '_', 'S', 'R', 'A', '_', 'R', '_', 'P', 'H', '_', 'W', 0,
  /* 13048 */ 'P', 'R', 'E', 'C', 'R', 'Q', '_', 'R', 'S', '_', 'P', 'H', '_', 'W', 0,
  /* 13063 */ 'S', 'U', 'B', 'Q', 'H', '_', 'W', 0,
  /* 13071 */ 'A', 'D', 'D', 'Q', 'H', '_', 'W', 0,
  /* 13079 */ 'S', 'R', 'A', 'I', '_', 'W', 0,
  /* 13086 */ 'S', 'L', 'D', 'I', '_', 'W', 0,
  /* 13093 */ 'B', 'N', 'E', 'G', 'I', '_', 'W', 0,
  /* 13101 */ 'S', 'L', 'L', 'I', '_', 'W', 0,
  /* 13108 */ 'S', 'R', 'L', 'I', '_', 'W', 0,
  /* 13115 */ 'B', 'I', 'N', 'S', 'L', 'I', '_', 'W', 0,
  /* 13124 */ 'C', 'E', 'Q', 'I', '_', 'W', 0,
  /* 13131 */ 'S', 'R', 'A', 'R', 'I', '_', 'W', 0,
  /* 13139 */ 'B', 'C', 'L', 'R', 'I', '_', 'W', 0,
  /* 13147 */ 'S', 'R', 'L', 'R', 'I', '_', 'W', 0,
  /* 13155 */ 'B', 'I', 'N', 'S', 'R', 'I', '_', 'W', 0,
  /* 13164 */ 'S', 'P', 'L', 'A', 'T', 'I', '_', 'W', 0,
  /* 13173 */ 'B', 'S', 'E', 'T', 'I', '_', 'W', 0,
  /* 13181 */ 'S', 'U', 'B', 'V', 'I', '_', 'W', 0,
  /* 13189 */ 'A', 'D', 'D', 'V', 'I', '_', 'W', 0,
  /* 13197 */ 'F', 'I', 'L', 'L', '_', 'W', 0,
  /* 13204 */ 'S', 'L', 'L', '_', 'W', 0,
  /* 13210 */ 'F', 'E', 'X', 'U', 'P', 'L', '_', 'W', 0,
  /* 13219 */ 'F', 'F', 'Q', 'L', '_', 'W', 0,
  /* 13226 */ 'S', 'R', 'L', '_', 'W', 0,
  /* 13232 */ 'B', 'I', 'N', 'S', 'L', '_', 'W', 0,
  /* 13240 */ 'F', 'M', 'U', 'L', '_', 'W', 0,
  /* 13247 */ 'I', 'L', 'V', 'L', '_', 'W', 0,
  /* 13254 */ 'D', 'P', 'A', 'Q', '_', 'S', 'A', '_', 'L', '_', 'W', 0,
  /* 13266 */ 'D', 'P', 'S', 'Q', '_', 'S', 'A', '_', 'L', '_', 'W', 0,
  /* 13278 */ 'F', 'M', 'I', 'N', '_', 'W', 0,
  /* 13285 */ 'F', 'C', 'U', 'N', '_', 'W', 0,
  /* 13292 */ 'F', 'S', 'U', 'N', '_', 'W', 0,
  /* 13299 */ 'F', 'E', 'X', 'D', 'O', '_', 'W', 0,
  /* 13307 */ 'F', 'R', 'C', 'P', '_', 'W', 0,
  /* 13314 */ 'F', 'C', 'E', 'Q', '_', 'W', 0,
  /* 13321 */ 'F', 'S', 'E', 'Q', '_', 'W', 0,
  /* 13328 */ 'F', 'C', 'U', 'E', 'Q', '_', 'W', 0,
  /* 13336 */ 'F', 'S', 'U', 'E', 'Q', '_', 'W', 0,
  /* 13344 */ 'F', 'T', 'Q', '_', 'W', 0,
  /* 13350 */ 'M', 'S', 'U', 'B', '_', 'Q', '_', 'W', 0,
  /* 13359 */ 'M', 'A', 'D', 'D', '_', 'Q', '_', 'W', 0,
  /* 13368 */ 'M', 'U', 'L', '_', 'Q', '_', 'W', 0,
  /* 13376 */ 'M', 'S', 'U', 'B', 'R', '_', 'Q', '_', 'W', 0,
  /* 13386 */ 'M', 'A', 'D', 'D', 'R', '_', 'Q', '_', 'W', 0,
  /* 13396 */ 'M', 'U', 'L', 'R', '_', 'Q', '_', 'W', 0,
  /* 13405 */ 'S', 'R', 'A', 'R', '_', 'W', 0,
  /* 13412 */ 'B', 'C', 'L', 'R', '_', 'W', 0,
  /* 13419 */ 'S', 'R', 'L', 'R', '_', 'W', 0,
  /* 13426 */ 'F', 'C', 'O', 'R', '_', 'W', 0,
  /* 13433 */ 'F', 'S', 'O', 'R', '_', 'W', 0,
  /* 13440 */ 'F', 'E', 'X', 'U', 'P', 'R', '_', 'W', 0,
  /* 13449 */ 'F', 'F', 'Q', 'R', '_', 'W', 0,
  /* 13456 */ 'B', 'I', 'N', 'S', 'R', '_', 'W', 0,
  /* 13464 */ 'E', 'X', 'T', 'R', '_', 'W', 0,
  /* 13471 */ 'I', 'L', 'V', 'R', '_', 'W', 0,
  /* 13478 */ 'S', 'H', 'R', 'A', '_', 'R', '_', 'W', 0,
  /* 13487 */ 'S', 'U', 'B', 'Q', 'H', '_', 'R', '_', 'W', 0,
  /* 13497 */ 'A', 'D', 'D', 'Q', 'H', '_', 'R', '_', 'W', 0,
  /* 13507 */ 'E', 'X', 'T', 'R', '_', 'R', '_', 'W', 0,
  /* 13516 */ 'S', 'H', 'R', 'A', 'V', '_', 'R', '_', 'W', 0,
  /* 13526 */ 'E', 'X', 'T', 'R', 'V', '_', 'R', '_', 'W', 0,
  /* 13536 */ 'F', 'A', 'B', 'S', '_', 'W', 0,
  /* 13543 */ 'M', 'U', 'L', 'Q', '_', 'R', 'S', '_', 'W', 0,
  /* 13553 */ 'E', 'X', 'T', 'R', '_', 'R', 'S', '_', 'W', 0,
  /* 13563 */ 'E', 'X', 'T', 'R', 'V', '_', 'R', 'S', '_', 'W', 0,
  /* 13574 */ 'F', 'C', 'L', 'A', 'S', 'S', '_', 'W', 0,
  /* 13583 */ 'A', 'S', 'U', 'B', '_', 'S', '_', 'W', 0,
  /* 13592 */ 'H', 'S', 'U', 'B', '_', 'S', '_', 'W', 0,
  /* 13601 */ 'D', 'P', 'S', 'U', 'B', '_', 'S', '_', 'W', 0,
  /* 13611 */ 'F', 'T', 'R', 'U', 'N', 'C', '_', 'S', '_', 'W', 0,
  /* 13622 */ 'H', 'A', 'D', 'D', '_', 'S', '_', 'W', 0,
  /* 13631 */ 'D', 'P', 'A', 'D', 'D', '_', 'S', '_', 'W', 0,
  /* 13641 */ 'M', 'O', 'D', '_', 'S', '_', 'W', 0,
  /* 13649 */ 'C', 'L', 'E', '_', 'S', '_', 'W', 0,
  /* 13657 */ 'A', 'V', 'E', '_', 'S', '_', 'W', 0,
  /* 13665 */ 'C', 'L', 'E', 'I', '_', 'S', '_', 'W', 0,
  /* 13674 */ 'M', 'I', 'N', 'I', '_', 'S', '_', 'W', 0,
  /* 13683 */ 'C', 'L', 'T', 'I', '_', 'S', '_', 'W', 0,
  /* 13692 */ 'M', 'A', 'X', 'I', '_', 'S', '_', 'W', 0,
  /* 13701 */ 'S', 'H', 'L', 'L', '_', 'S', '_', 'W', 0,
  /* 13710 */ 'M', 'I', 'N', '_', 'S', '_', 'W', 0,
  /* 13718 */ 'D', 'O', 'T', 'P', '_', 'S', '_', 'W', 0,
  /* 13727 */ 'S', 'U', 'B', 'Q', '_', 'S', '_', 'W', 0,
  /* 13736 */ 'A', 'D', 'D', 'Q', '_', 'S', '_', 'W', 0,
  /* 13745 */ 'M', 'U', 'L', 'Q', '_', 'S', '_', 'W', 0,
  /* 13754 */ 'A', 'B', 'S', 'Q', '_', 'S', '_', 'W', 0,
  /* 13763 */ 'A', 'V', 'E', 'R', '_', 'S', '_', 'W', 0,
  /* 13772 */ 'S', 'U', 'B', 'S', '_', 'S', '_', 'W', 0,
  /* 13781 */ 'A', 'D', 'D', 'S', '_', 'S', '_', 'W', 0,
  /* 13790 */ 'S', 'A', 'T', '_', 'S', '_', 'W', 0,
  /* 13798 */ 'C', 'L', 'T', '_', 'S', '_', 'W', 0,
  /* 13806 */ 'F', 'F', 'I', 'N', 'T', '_', 'S', '_', 'W', 0,
  /* 13816 */ 'F', 'T', 'I', 'N', 'T', '_', 'S', '_', 'W', 0,
  /* 13826 */ 'P', 's', 'e', 'u', 'd', 'o', 'C', 'V', 'T', '_', 'S', '_', 'W', 0,
  /* 13840 */ 'S', 'U', 'B', 'S', 'U', 'U', '_', 'S', '_', 'W', 0,
  /* 13851 */ 'D', 'I', 'V', '_', 'S', '_', 'W', 0,
  /* 13859 */ 'S', 'H', 'L', 'L', 'V', '_', 'S', '_', 'W', 0,
  /* 13869 */ 'M', 'A', 'X', '_', 'S', '_', 'W', 0,
  /* 13877 */ 'C', 'O', 'P', 'Y', '_', 'S', '_', 'W', 0,
  /* 13886 */ 'S', 'P', 'L', 'A', 'T', '_', 'W', 0,
  /* 13894 */ 'B', 'S', 'E', 'T', '_', 'W', 0,
  /* 13901 */ 'F', 'C', 'L', 'T', '_', 'W', 0,
  /* 13908 */ 'F', 'S', 'L', 'T', '_', 'W', 0,
  /* 13915 */ 'F', 'C', 'U', 'L', 'T', '_', 'W', 0,
  /* 13923 */ 'F', 'S', 'U', 'L', 'T', '_', 'W', 0,
  /* 13931 */ 'P', 'C', 'N', 'T', '_', 'W', 0,
  /* 13938 */ 'F', 'R', 'I', 'N', 'T', '_', 'W', 0,
  /* 13946 */ 'I', 'N', 'S', 'E', 'R', 'T', '_', 'W', 0,
  /* 13955 */ 'F', 'S', 'Q', 'R', 'T', '_', 'W', 0,
  /* 13963 */ 'F', 'R', 'S', 'Q', 'R', 'T', '_', 'W', 0,
  /* 13972 */ 'S', 'T', '_', 'W', 0,
  /* 13977 */ 'A', 'S', 'U', 'B', '_', 'U', '_', 'W', 0,
  /* 13986 */ 'H', 'S', 'U', 'B', '_', 'U', '_', 'W', 0,
  /* 13995 */ 'D', 'P', 'S', 'U', 'B', '_', 'U', '_', 'W', 0,
  /* 14005 */ 'F', 'T', 'R', 'U', 'N', 'C', '_', 'U', '_', 'W', 0,
  /* 14016 */ 'H', 'A', 'D', 'D', '_', 'U', '_', 'W', 0,
  /* 14025 */ 'D', 'P', 'A', 'D', 'D', '_', 'U', '_', 'W', 0,
  /* 14035 */ 'M', 'O', 'D', '_', 'U', '_', 'W', 0,
  /* 14043 */ 'C', 'L', 'E', '_', 'U', '_', 'W', 0,
  /* 14051 */ 'A', 'V', 'E', '_', 'U', '_', 'W', 0,
  /* 14059 */ 'C', 'L', 'E', 'I', '_', 'U', '_', 'W', 0,
  /* 14068 */ 'M', 'I', 'N', 'I', '_', 'U', '_', 'W', 0,
  /* 14077 */ 'C', 'L', 'T', 'I', '_', 'U', '_', 'W', 0,
  /* 14086 */ 'M', 'A', 'X', 'I', '_', 'U', '_', 'W', 0,
  /* 14095 */ 'M', 'I', 'N', '_', 'U', '_', 'W', 0,
  /* 14103 */ 'D', 'O', 'T', 'P', '_', 'U', '_', 'W', 0,
  /* 14112 */ 'A', 'V', 'E', 'R', '_', 'U', '_', 'W', 0,
  /* 14121 */ 'S', 'U', 'B', 'S', '_', 'U', '_', 'W', 0,
  /* 14130 */ 'A', 'D', 'D', 'S', '_', 'U', '_', 'W', 0,
  /* 14139 */ 'S', 'U', 'B', 'S', 'U', 'S', '_', 'U', '_', 'W', 0,
  /* 14150 */ 'S', 'A', 'T', '_', 'U', '_', 'W', 0,
  /* 14158 */ 'C', 'L', 'T', '_', 'U', '_', 'W', 0,
  /* 14166 */ 'F', 'F', 'I', 'N', 'T', '_', 'U', '_', 'W', 0,
  /* 14176 */ 'F', 'T', 'I', 'N', 'T', '_', 'U', '_', 'W', 0,
  /* 14186 */ 'D', 'I', 'V', '_', 'U', '_', 'W', 0,
  /* 14194 */ 'M', 'A', 'X', '_', 'U', '_', 'W', 0,
  /* 14202 */ 'C', 'O', 'P', 'Y', '_', 'U', '_', 'W', 0,
  /* 14211 */ 'M', 'S', 'U', 'B', 'V', '_', 'W', 0,
  /* 14219 */ 'M', 'A', 'D', 'D', 'V', '_', 'W', 0,
  /* 14227 */ 'P', 'C', 'K', 'E', 'V', '_', 'W', 0,
  /* 14235 */ 'I', 'L', 'V', 'E', 'V', '_', 'W', 0,
  /* 14243 */ 'F', 'D', 'I', 'V', '_', 'W', 0,
  /* 14250 */ 'M', 'U', 'L', 'V', '_', 'W', 0,
  /* 14257 */ 'E', 'X', 'T', 'R', 'V', '_', 'W', 0,
  /* 14265 */ 'F', 'M', 'A', 'X', '_', 'W', 0,
  /* 14272 */ 'B', 'Z', '_', 'W', 0,
  /* 14277 */ 'B', 'N', 'Z', '_', 'W', 0,
  /* 14283 */ 'L', 'H', 'X', 0,
  /* 14287 */ 'J', 'A', 'L', 'X', 0,
  /* 14292 */ 'L', 'B', 'U', 'X', 0,
  /* 14297 */ 'L', 'W', 'X', 0,
  /* 14301 */ 'C', 'O', 'P', 'Y', 0,
  /* 14306 */ 'C', 'O', 'N', 'S', 'T', 'P', 'O', 'O', 'L', '_', 'E', 'N', 'T', 'R', 'Y', 0,
  /* 14322 */ 'B', 'G', 'E', 'Z', 0,
  /* 14327 */ 'B', 'L', 'E', 'Z', 0,
  /* 14332 */ 'B', 'C', '1', 'N', 'E', 'Z', 0,
  /* 14339 */ 'B', 'C', '2', 'N', 'E', 'Z', 0,
  /* 14346 */ 'S', 'E', 'L', 'N', 'E', 'Z', 0,
  /* 14353 */ 'D', 'C', 'L', 'Z', 0,
  /* 14358 */ 'B', 'C', '1', 'E', 'Q', 'Z', 0,
  /* 14365 */ 'B', 'C', '2', 'E', 'Q', 'Z', 0,
  /* 14372 */ 'S', 'E', 'L', 'E', 'Q', 'Z', 0,
  /* 14379 */ 'B', 'G', 'T', 'Z', 0,
  /* 14384 */ 'B', 'L', 'T', 'Z', 0,
  /* 14389 */ 'S', 'e', 'l', 'B', 'n', 'e', 'Z', 0,
  /* 14397 */ 'S', 'e', 'l', 'B', 'e', 'q', 'Z', 0,
  /* 14405 */ 'L', 'o', 'a', 'd', 'I', 'm', 'm', '3', '2', 'R', 'e', 'g', 0,
  /* 14418 */ 'L', 'o', 'a', 'd', 'A', 'd', 'd', 'r', '3', '2', 'R', 'e', 'g', 0,
  /* 14432 */ 'L', 'o', 'a', 'd', 'I', 'm', 'm', '6', '4', 'R', 'e', 'g', 0,
  /* 14445 */ 'P', 's', 'e', 'u', 'd', 'o', 'I', 'n', 'd', 'i', 'r', 'e', 'c', 't', 'B', 'r', 'a', 'n', 'c', 'h', 0,
  /* 14466 */ 'D', 'A', 'D', 'D', 'i', 0,
  /* 14472 */ 'A', 'N', 'D', 'i', 0,
  /* 14477 */ 'S', 'N', 'E', 'i', 0,
  /* 14482 */ 'S', 'E', 'Q', 'i', 0,
  /* 14487 */ 'X', 'O', 'R', 'i', 0,
  /* 14492 */ 'S', 'L', 'T', 'i', 0,
  /* 14497 */ 'L', 'O', 'N', 'G', '_', 'B', 'R', 'A', 'N', 'C', 'H', '_', 'L', 'U', 'i', 0,
  /* 14513 */ 'S', 'e', 'l', 'T', 'B', 't', 'n', 'e', 'Z', 'C', 'm', 'p', 'i', 0,
  /* 14527 */ 'S', 'e', 'l', 'T', 'B', 't', 'e', 'q', 'Z', 'C', 'm', 'p', 'i', 0,
  /* 14541 */ 'S', 'e', 'l', 'T', 'B', 't', 'n', 'e', 'Z', 'S', 'l', 't', 'i', 0,
  /* 14555 */ 'S', 'e', 'l', 'T', 'B', 't', 'e', 'q', 'Z', 'S', 'l', 't', 'i', 0,
  /* 14569 */ 'L', 'o', 'a', 'd', 'A', 'd', 'd', 'r', '3', '2', 'I', 'm', 'm', 0,
  /* 14583 */ 'P', 's', 'e', 'u', 'd', 'o', 'R', 'e', 't', 'u', 'r', 'n', 0,
  /* 14596 */ 'J', 'A', 'L', 'R', '6', '4', 'P', 's', 'e', 'u', 'd', 'o', 0,
  /* 14609 */ 'J', 'A', 'L', 'R', 'P', 's', 'e', 'u', 'd', 'o', 0,
  /* 14620 */ 'S', 'e', 'l', 'T', 'B', 't', 'n', 'e', 'Z', 'C', 'm', 'p', 0,
  /* 14633 */ 'S', 'e', 'l', 'T', 'B', 't', 'e', 'q', 'Z', 'C', 'm', 'p', 0,
  /* 14646 */ 'S', 'e', 'l', 'T', 'B', 't', 'n', 'e', 'Z', 'S', 'l', 't', 0,
  /* 14659 */ 'S', 'e', 'l', 'T', 'B', 't', 'e', 'q', 'Z', 'S', 'l', 't', 0,
  /* 14672 */ 'L', 'B', 'u', 0,
  /* 14676 */ 'D', 'S', 'U', 'B', 'u', 0,
  /* 14682 */ 'B', 'A', 'D', 'D', 'u', 0,
  /* 14688 */ 'D', 'A', 'D', 'D', 'u', 0,
  /* 14694 */ 'L', 'H', 'u', 0,
  /* 14698 */ 'S', 'L', 'T', 'u', 0,
  /* 14703 */ 'P', 's', 'e', 'u', 'd', 'o', 'D', 'M', 'U', 'L', 'T', 'u', 0,
  /* 14716 */ 'P', 's', 'e', 'u', 'd', 'o', 'M', 'U', 'L', 'T', 'u', 0,
  /* 14728 */ 'L', 'W', 'u', 0,
  /* 14732 */ 'L', 'O', 'N', 'G', '_', 'B', 'R', 'A', 'N', 'C', 'H', '_', 'D', 'A', 'D', 'D', 'i', 'u', 0,
  /* 14751 */ 'L', 'E', 'A', '_', 'A', 'D', 'D', 'i', 'u', 0,
  /* 14761 */ 'L', 'O', 'N', 'G', '_', 'B', 'R', 'A', 'N', 'C', 'H', '_', 'A', 'D', 'D', 'i', 'u', 0,
  /* 14779 */ 'S', 'L', 'T', 'i', 'u', 0,
  /* 14785 */ 'S', 'e', 'l', 'T', 'B', 't', 'n', 'e', 'Z', 'S', 'l', 't', 'i', 'u', 0,
  /* 14800 */ 'S', 'e', 'l', 'T', 'B', 't', 'e', 'q', 'Z', 'S', 'l', 't', 'i', 'u', 0,
  /* 14815 */ 'S', 'e', 'l', 'T', 'B', 't', 'n', 'e', 'Z', 'S', 'l', 't', 'u', 0,
  /* 14829 */ 'S', 'e', 'l', 'T', 'B', 't', 'e', 'q', 'Z', 'S', 'l', 't', 'u', 0,
};

extern const unsigned MipsInstrNameIndices[] = {
    8227U, 10524U, 10560U, 8482U, 8473U, 8587U, 6717U, 6732U, 
    6699U, 6746U, 11721U, 6684U, 6636U, 14301U, 6659U, 12466U, 
    5230U, 11224U, 12455U, 5248U, 12444U, 5053U, 7050U, 4083U, 
    13754U, 5187U, 5083U, 9673U, 8943U, 8967U, 9686U, 6851U, 
    6968U, 13497U, 13071U, 6923U, 7030U, 13736U, 5107U, 4261U, 
    5321U, 7330U, 12824U, 4669U, 6108U, 7819U, 13781U, 4861U, 
    6473U, 8068U, 14130U, 9184U, 3951U, 4061U, 7115U, 4163U, 
    7070U, 4103U, 4475U, 5685U, 7515U, 13189U, 4931U, 6563U, 
    8138U, 14220U, 5140U, 4245U, 5304U, 7314U, 12807U, 9321U, 
    14467U, 10416U, 14745U, 10506U, 14683U, 10470U, 10576U, 11480U, 
    10547U, 5076U, 5211U, 8995U, 960U, 9022U, 4350U, 9336U, 
    12691U, 10744U, 10828U, 10999U, 14472U, 2073U, 10424U, 5223U, 
    4574U, 5955U, 7668U, 13583U, 4766U, 6320U, 7926U, 13977U, 
    2292U, 670U, 1754U, 3719U, 2215U, 593U, 1625U, 3646U, 
    2256U, 634U, 1666U, 3685U, 2235U, 613U, 1645U, 3665U, 
    2332U, 710U, 1794U, 3757U, 2195U, 573U, 1605U, 3627U, 
    2312U, 690U, 1774U, 3738U, 2276U, 654U, 1738U, 3704U, 
    8252U, 5070U, 4651U, 6090U, 7792U, 13763U, 4843U, 6455U, 
    8050U, 14112U, 4599U, 6029U, 7731U, 13657U, 4791U, 6394U, 
    7989U, 14051U, 2734U, 2610U, 3118U, 2762U, 2559U, 3058U, 
    2626U, 3421U, 3360U, 3869U, 14682U, 8377U, 4989U, 10546U, 
    11578U, 4972U, 14358U, 6694U, 8496U, 9382U, 14332U, 12397U, 
    8607U, 10110U, 14365U, 14339U, 4411U, 5635U, 7465U, 13139U, 
    4545U, 5880U, 7639U, 13412U, 11495U, 1892U, 5102U, 8597U, 
    9229U, 5024U, 5164U, 9311U, 9727U, 4975U, 5118U, 14322U, 
    1958U, 8385U, 5000U, 8571U, 9833U, 9557U, 5146U, 8626U, 
    10377U, 14379U, 1990U, 5032U, 5170U, 8638U, 10400U, 4387U, 
    5611U, 7441U, 13115U, 4517U, 5734U, 7542U, 13232U, 4441U, 
    5651U, 7481U, 13155U, 4559U, 5924U, 7653U, 13456U, 12588U, 
    11239U, 14327U, 1965U, 5008U, 5152U, 8632U, 10385U, 5113U, 
    5124U, 14384U, 1997U, 8392U, 5040U, 8579U, 9844U, 9567U, 
    5176U, 8644U, 10408U, 4490U, 12740U, 4483U, 12728U, 6666U, 
    1491U, 4980U, 4357U, 5589U, 7419U, 13093U, 4329U, 5568U, 
    7398U, 12997U, 8491U, 9219U, 5016U, 5158U, 9302U, 9359U, 
    5130U, 4966U, 6621U, 8173U, 12734U, 14277U, 5135U, 564U, 
    10627U, 8371U, 9050U, 9541U, 4365U, 10730U, 10668U, 10923U, 
    10814U, 12704U, 10985U, 4459U, 5669U, 7499U, 13173U, 4738U, 
    6197U, 7898U, 13894U, 4961U, 6607U, 8168U, 12723U, 14272U, 
    3145U, 2791U, 3157U, 2804U, 3133U, 2778U, 3044U, 3469U, 
    2855U, 2402U, 2883U, 2432U, 2913U, 2944U, 2968U, 3461U, 
    2841U, 2387U, 2869U, 2417U, 2897U, 2929U, 2959U, 1497U, 
    2004U, 6653U, 9350U, 3546U, 1221U, 12048U, 531U, 1458U, 
    10336U, 12346U, 10074U, 4396U, 5620U, 7450U, 13124U, 4532U, 
    5804U, 7565U, 13315U, 37U, 8696U, 3853U, 11711U, 751U, 
    5947U, 12177U, 4607U, 6037U, 7739U, 13665U, 4799U, 6402U, 
    7997U, 14059U, 4591U, 6021U, 7723U, 13649U, 4783U, 6386U, 
    7981U, 14043U, 11198U, 9624U, 3578U, 4625U, 6055U, 7757U, 
    13683U, 4817U, 6420U, 8015U, 14077U, 4686U, 6125U, 7836U, 
    13798U, 4889U, 6501U, 8096U, 14158U, 14354U, 10393U, 3595U, 
    3998U, 3900U, 4113U, 4011U, 3913U, 4126U, 4029U, 3931U, 
    4144U, 5864U, 6937U, 12161U, 5560U, 11974U, 5466U, 6832U, 
    11900U, 6265U, 7097U, 12262U, 5527U, 11909U, 5817U, 12115U, 
    5419U, 11854U, 6218U, 12216U, 5843U, 12125U, 5445U, 11864U, 
    6244U, 12226U, 5777U, 12081U, 5854U, 12144U, 5456U, 11883U, 
    6255U, 12245U, 5787U, 12098U, 14306U, 10715U, 10970U, 4721U, 
    6180U, 7881U, 13877U, 4913U, 6545U, 8120U, 14202U, 48U, 
    8730U, 3860U, 11743U, 12759U, 10301U, 8656U, 11753U, 12791U, 
    9921U, 1244U, 8954U, 12067U, 9986U, 383U, 8876U, 1310U, 
    8672U, 13832U, 10357U, 554U, 1481U, 10368U, 12365U, 10099U, 
    365U, 1292U, 12154U, 248U, 1118U, 11949U, 221U, 1091U, 
    11893U, 440U, 1367U, 12255U, 180U, 1050U, 11829U, 190U, 
    1060U, 11837U, 308U, 1178U, 12013U, 410U, 1337U, 12200U, 
    201U, 1071U, 11846U, 420U, 1347U, 12208U, 345U, 1272U, 
    12107U, 230U, 1100U, 11935U, 355U, 1282U, 12136U, 211U, 
    1081U, 11875U, 430U, 1357U, 12237U, 327U, 1254U, 12091U, 
    3242U, 3081U, 2708U, 802U, 5186U, 14466U, 14744U, 14688U, 
    8198U, 10553U, 8241U, 8251U, 11238U, 11197U, 3577U, 14353U, 
    3594U, 12595U, 12576U, 12402U, 10118U, 12481U, 10540U, 12570U, 
    8185U, 11716U, 10534U, 12559U, 12596U, 12577U, 4705U, 6164U, 
    7855U, 13851U, 4897U, 6529U, 8104U, 14186U, 9433U, 3848U, 
    3509U, 0U, 42U, 823U, 5243U, 12510U, 6U, 53U, 
    829U, 7303U, 12521U, 8613U, 12427U, 14709U, 12547U, 3569U, 
    6081U, 7783U, 13718U, 6446U, 8041U, 14103U, 6003U, 7705U, 
    13631U, 6368U, 7963U, 14025U, 7179U, 7254U, 13254U, 7216U, 
    8443U, 11556U, 7280U, 7159U, 11278U, 7193U, 7267U, 13266U, 
    7242U, 5973U, 7686U, 13601U, 6338U, 7944U, 13995U, 8454U, 
    11567U, 7290U, 7207U, 11661U, 743U, 12679U, 6760U, 12606U, 
    5202U, 8592U, 729U, 774U, 12646U, 3837U, 115U, 12582U, 
    8602U, 736U, 12652U, 4223U, 14676U, 12629U, 3328U, 3306U, 
    3871U, 9253U, 8190U, 9441U, 12403U, 10119U, 12482U, 11475U, 
    11258U, 12665U, 12673U, 13563U, 13526U, 7863U, 14257U, 13553U, 
    13507U, 7801U, 13464U, 11738U, 758U, 10166U, 1510U, 2020U, 
    5939U, 374U, 1301U, 9817U, 12170U, 9997U, 13536U, 5368U, 
    161U, 1031U, 9320U, 11814U, 9900U, 12871U, 5513U, 12976U, 
    5803U, 13314U, 5946U, 13574U, 5405U, 12908U, 6204U, 13901U, 
    336U, 8864U, 1263U, 765U, 8931U, 5475U, 12938U, 5894U, 
    13426U, 5827U, 13328U, 5429U, 12922U, 6228U, 13915U, 5489U, 
    12952U, 5763U, 13285U, 6586U, 489U, 1416U, 10240U, 12312U, 
    10028U, 14243U, 7557U, 13299U, 5276U, 10593U, 12777U, 10610U, 
    5712U, 13210U, 5908U, 13440U, 6133U, 13806U, 6509U, 14166U, 
    5721U, 13219U, 5917U, 13449U, 4498U, 5699U, 10683U, 10938U, 
    7523U, 13197U, 5268U, 12769U, 1232U, 12057U, 542U, 1469U, 
    10346U, 12355U, 10086U, 5375U, 12878U, 5330U, 12833U, 6600U, 
    14265U, 5312U, 12815U, 5756U, 13278U, 498U, 8901U, 1425U, 
    12319U, 10038U, 5346U, 12849U, 5742U, 318U, 1188U, 9602U, 
    12021U, 9976U, 13240U, 277U, 1147U, 9398U, 11982U, 9942U, 
    5796U, 13307U, 6281U, 13938U, 6306U, 13963U, 5520U, 12983U, 
    5810U, 13321U, 5412U, 12915U, 6211U, 13908U, 5482U, 12945U, 
    5901U, 13433U, 6298U, 449U, 1376U, 10157U, 12278U, 10007U, 
    13955U, 5339U, 142U, 1012U, 9272U, 11799U, 9879U, 12842U, 
    5835U, 13336U, 5437U, 12930U, 6236U, 13923U, 5497U, 12960U, 
    5770U, 13292U, 6143U, 13816U, 6519U, 14176U, 7571U, 13344U, 
    5983U, 13611U, 6348U, 14005U, 3002U, 5994U, 7696U, 13622U, 
    6359U, 7954U, 14016U, 5964U, 7677U, 13592U, 6329U, 7935U, 
    13986U, 4946U, 6578U, 8153U, 14235U, 4525U, 5749U, 7550U, 
    13247U, 4306U, 5397U, 7375U, 12900U, 4567U, 5932U, 7661U, 
    13471U, 11712U, 4752U, 11069U, 6289U, 11112U, 10698U, 11090U, 
    10953U, 11154U, 7912U, 11133U, 13946U, 11176U, 12686U, 4314U, 
    5505U, 7383U, 12968U, 9855U, 8369U, 8381U, 11648U, 9126U, 
    1903U, 14596U, 14609U, 9145U, 9862U, 3881U, 9755U, 9825U, 
    14287U, 9550U, 4994U, 4985U, 11645U, 9118U, 1898U, 11465U, 
    8986U, 3875U, 3517U, 9749U, 9536U, 3052U, 2188U, 2985U, 
    2977U, 3191U, 3023U, 3889U, 927U, 9165U, 14292U, 9260U, 
    14672U, 2131U, 10455U, 5208U, 27U, 875U, 8680U, 813U, 
    3477U, 855U, 4344U, 5583U, 7413U, 13087U, 8465U, 5065U, 
    11585U, 69U, 889U, 4293U, 5384U, 7362U, 12887U, 14751U, 
    2150U, 10502U, 6774U, 1534U, 9194U, 14283U, 9421U, 14694U, 
    2137U, 10478U, 9042U, 8560U, 5207U, 3539U, 9582U, 3563U, 
    3602U, 937U, 11283U, 11342U, 14761U, 14732U, 14497U, 3849U, 
    3510U, 81U, 905U, 8762U, 14509U, 2094U, 10448U, 12747U, 
    9203U, 1948U, 59U, 8746U, 835U, 3493U, 865U, 8618U, 
    1860U, 9610U, 9079U, 8913U, 5097U, 9713U, 11679U, 1930U, 
    9803U, 9697U, 5091U, 10225U, 14297U, 93U, 8780U, 9871U, 
    10289U, 14728U, 2461U, 2525U, 2493U, 2542U, 3071U, 2812U, 
    2697U, 14569U, 14418U, 14405U, 14432U, 800U, 3171U, 2828U, 
    2578U, 2640U, 5197U, 5545U, 11927U, 7613U, 13386U, 12504U, 
    11445U, 10182U, 4930U, 6562U, 8137U, 14219U, 171U, 8812U, 
    1041U, 11333U, 9328U, 7586U, 13359U, 11822U, 9911U, 8502U, 
    11593U, 8528U, 11619U, 5297U, 11792U, 4634U, 6064U, 7766U, 
    13692U, 4826U, 6429U, 8024U, 14086U, 4270U, 5331U, 7339U, 
    12834U, 6601U, 12373U, 4713U, 6172U, 7873U, 13869U, 4905U, 
    6537U, 8112U, 14194U, 1U, 43U, 8704U, 824U, 122U, 
    966U, 8712U, 8209U, 9032U, 1550U, 11373U, 9455U, 11208U, 
    9097U, 1878U, 11408U, 9631U, 5284U, 11785U, 4616U, 6046U, 
    7748U, 13674U, 4808U, 6411U, 8006U, 14068U, 4253U, 5313U, 
    7322U, 12816U, 5757U, 12075U, 4643U, 6073U, 7775U, 13710U, 
    4835U, 6438U, 8033U, 14095U, 784U, 2115U, 5244U, 4221U, 
    12511U, 4583U, 6013U, 7715U, 13641U, 4775U, 6378U, 7973U, 
    14035U, 9004U, 12697U, 239U, 8824U, 1109U, 8284U, 1686U, 
    9496U, 11942U, 9932U, 986U, 8262U, 1579U, 11763U, 286U, 
    8836U, 1156U, 8310U, 1716U, 9506U, 11989U, 9952U, 459U, 
    8889U, 1386U, 8343U, 1830U, 9516U, 12286U, 10018U, 999U, 
    8273U, 1592U, 11774U, 297U, 8850U, 1167U, 8319U, 1727U, 
    9526U, 11998U, 9964U, 4234U, 5537U, 11919U, 7603U, 13376U, 
    12492U, 11435U, 10173U, 4922U, 6554U, 8129U, 14211U, 152U, 
    8799U, 1022U, 11324U, 9280U, 7577U, 13350U, 11807U, 9890U, 
    7U, 54U, 8738U, 830U, 132U, 976U, 8721U, 8231U, 
    1572U, 11399U, 9463U, 11265U, 11219U, 1885U, 11417U, 9639U, 
    17U, 105U, 845U, 22U, 110U, 850U, 7304U, 12522U, 
    8614U, 8540U, 11631U, 8399U, 11512U, 6990U, 13543U, 7040U, 
    13745U, 7623U, 13396U, 7228U, 7168U, 12428U, 11455U, 11426U, 
    10149U, 14710U, 10493U, 12542U, 4954U, 6593U, 8161U, 14250U, 
    9603U, 6908U, 7595U, 13368U, 3570U, 7011U, 3037U, 3164U, 
    2351U, 2170U, 3262U, 3395U, 3294U, 3447U, 4278U, 5354U, 
    7347U, 12857U, 4285U, 5361U, 7354U, 12864U, 170U, 8811U, 
    1040U, 11821U, 9910U, 151U, 8798U, 1021U, 11806U, 9889U, 
    11274U, 11653U, 1910U, 4427U, 9763U, 12711U, 10759U, 10843U, 
    11014U, 9156U, 3232U, 3273U, 11654U, 9137U, 1911U, 4428U, 
    9764U, 12712U, 10760U, 10844U, 11015U, 14488U, 2081U, 10433U, 
    3372U, 6898U, 6678U, 9373U, 4938U, 6570U, 8145U, 14227U, 
    4298U, 5389U, 7367U, 12892U, 4745U, 6274U, 7905U, 13931U, 
    6866U, 3966U, 11279U, 8428U, 3790U, 11541U, 3821U, 8515U, 
    11606U, 8414U, 3775U, 11527U, 3806U, 6810U, 13019U, 6785U, 
    13048U, 6798U, 13004U, 13031U, 6712U, 9390U, 3555U, 5215U, 
    4023U, 3925U, 4138U, 6931U, 6826U, 7091U, 12753U, 8650U, 
    12785U, 8666U, 13826U, 12421U, 14703U, 12600U, 12623U, 14445U, 
    2050U, 5191U, 12498U, 8203U, 1544U, 11202U, 1872U, 4228U, 
    12486U, 8214U, 1557U, 11382U, 12433U, 14716U, 6860U, 3960U, 
    14583U, 2100U, 12612U, 256U, 1126U, 8291U, 1695U, 11955U, 
    468U, 1395U, 8350U, 1839U, 12293U, 393U, 1320U, 8328U, 
    1813U, 12185U, 12635U, 4207U, 11312U, 11673U, 1922U, 9794U, 
    7141U, 4189U, 6882U, 3982U, 6282U, 12271U, 11662U, 12680U, 
    10280U, 9777U, 1209U, 12038U, 519U, 1446U, 10325U, 12336U, 
    10061U, 2992U, 2368U, 3842U, 2180U, 4678U, 6117U, 7828U, 
    13790U, 4881U, 6493U, 8088U, 14150U, 4218U, 8978U, 932U, 
    9266U, 5110U, 5182U, 3532U, 9296U, 3526U, 5265U, 11247U, 
    9107U, 9647U, 3585U, 32U, 882U, 8688U, 818U, 3485U, 
    860U, 12607U, 10248U, 8469U, 11589U, 75U, 897U, 3867U, 
    921U, 9246U, 6770U, 1528U, 9414U, 14372U, 1981U, 6627U, 
    12388U, 14346U, 1972U, 6612U, 12379U, 5693U, 12007U, 11499U, 
    14482U, 7300U, 9014U, 1539U, 4323U, 7392U, 12991U, 11213U, 
    12658U, 7132U, 4180U, 7080U, 13859U, 6874U, 3974U, 7001U, 
    13701U, 7123U, 4171U, 6979U, 4072U, 13516U, 6777U, 3892U, 
    6947U, 4040U, 13478U, 7150U, 4198U, 6890U, 3990U, 9427U, 
    4343U, 5582U, 7412U, 13086U, 4292U, 5383U, 7361U, 12886U, 
    8593U, 9061U, 775U, 2041U, 4373U, 5597U, 7427U, 13101U, 
    12647U, 10264U, 4505U, 5706U, 7530U, 9588U, 13204U, 12413U, 
    1942U, 10135U, 14492U, 2087U, 10440U, 14779U, 2162U, 10515U, 
    14698U, 2143U, 10485U, 6670U, 14477U, 10643U, 10789U, 10873U, 
    10898U, 11044U, 4450U, 5660U, 7490U, 13164U, 4730U, 6189U, 
    7890U, 13886U, 3838U, 4336U, 5575U, 7405U, 13079U, 4403U, 
    5627U, 7457U, 13131U, 4538U, 5873U, 7632U, 13405U, 12583U, 
    10232U, 4239U, 5291U, 7308U, 9239U, 12801U, 8603U, 9070U, 
    4380U, 5604U, 7434U, 13108U, 4419U, 5643U, 7473U, 13147U, 
    4552U, 5887U, 7646U, 13419U, 12653U, 10272U, 4511U, 5728U, 
    7536U, 9595U, 13226U, 11272U, 9664U, 3614U, 948U, 11297U, 
    11357U, 4761U, 6315U, 7921U, 13972U, 4224U, 6842U, 6957U, 
    13487U, 13063U, 6915U, 7020U, 13727U, 4870U, 6482U, 8077U, 
    14139U, 4694U, 6153U, 7844U, 13840U, 4660U, 6099U, 7810U, 
    13772U, 4852U, 6464U, 8059U, 14121U, 9174U, 3942U, 4050U, 
    7107U, 4155U, 7060U, 4093U, 4467U, 5677U, 7507U, 13181U, 
    4923U, 6555U, 8130U, 14212U, 9273U, 14677U, 10462U, 87U, 
    913U, 8771U, 12750U, 9211U, 1953U, 64U, 8754U, 840U, 
    3501U, 870U, 8622U, 1866U, 9617U, 9088U, 8922U, 9720U, 
    11683U, 1936U, 9810U, 9705U, 99U, 8789U, 10295U, 5048U, 
    8179U, 9288U, 8563U, 9577U, 10656U, 10802U, 10886U, 10911U, 
    11057U, 3016U, 2379U, 2477U, 3183U, 3199U, 14397U, 14389U, 
    14633U, 14527U, 14659U, 14555U, 14800U, 14829U, 14620U, 14513U, 
    14646U, 14541U, 14785U, 14815U, 2509U, 2447U, 3338U, 3207U, 
    3252U, 2666U, 3093U, 2721U, 2681U, 3105U, 2748U, 3219U, 
    3283U, 3434U, 2361U, 3317U, 2454U, 3349U, 3408U, 2594U, 
    2653U, 8554U, 11687U, 11700U, 11503U, 8236U, 9471U, 9734U, 
    6649U, 8188U, 12527U, 10199U, 9439U, 12516U, 10191U, 9343U, 
    11253U, 9656U, 11507U, 9741U, 8256U, 9487U, 11667U, 9785U, 
    12417U, 8246U, 10208U, 9479U, 12565U, 10217U, 10142U, 6674U, 
    8193U, 9447U, 9366U, 11233U, 1197U, 12028U, 507U, 1434U, 
    10314U, 12326U, 10048U, 12533U, 12630U, 10256U, 12540U, 12U, 
    12553U, 4322U, 5553U, 7391U, 12990U, 12408U, 10127U, 11318U, 
    6765U, 9406U, 11657U, 9136U, 1916U, 4434U, 9770U, 12717U, 
    10774U, 10858U, 11029U, 14487U, 2080U, 10432U, 3383U, 
};

static inline void InitMipsMCInstrInfo(MCInstrInfo *II) {
  II->InitMCInstrInfo(MipsInsts, MipsInstrNameIndices, MipsInstrNameData, 1759);
}

} // End llvm namespace 
#endif // GET_INSTRINFO_MC_DESC


#ifdef GET_INSTRINFO_HEADER
#undef GET_INSTRINFO_HEADER
namespace llvm {
struct MipsGenInstrInfo : public TargetInstrInfo {
  explicit MipsGenInstrInfo(int SO = -1, int DO = -1);
  virtual ~MipsGenInstrInfo();
};
} // End llvm namespace 
#endif // GET_INSTRINFO_HEADER


#ifdef GET_INSTRINFO_CTOR_DTOR
#undef GET_INSTRINFO_CTOR_DTOR
namespace llvm {
extern const MCInstrDesc MipsInsts[];
extern const unsigned MipsInstrNameIndices[];
extern const char MipsInstrNameData[];
MipsGenInstrInfo::MipsGenInstrInfo(int SO, int DO)
  : TargetInstrInfo(SO, DO) {
  InitMCInstrInfo(MipsInsts, MipsInstrNameIndices, MipsInstrNameData, 1759);
}
MipsGenInstrInfo::~MipsGenInstrInfo() {}
} // End llvm namespace 
#endif // GET_INSTRINFO_CTOR_DTOR

#ifdef GET_INSTRINFO_OPERAND_ENUM
#undef GET_INSTRINFO_OPERAND_ENUM
namespace llvm {namespace Mips {
namespace OpName { 
enum {
OPERAND_LAST
};
} // End namespace OpName
} // End namespace Mips
} // End namespace llvm
#endif //GET_INSTRINFO_OPERAND_ENUM
#ifdef GET_INSTRINFO_NAMED_OPS
#undef GET_INSTRINFO_NAMED_OPS
namespace llvm {namespace Mips {
LLVM_READONLY
int16_t getNamedOperandIdx(uint16_t Opcode, uint16_t NamedIdx) {
  return -1;
}
} // End namespace Mips
} // End namespace llvm
#endif //GET_INSTRINFO_NAMED_OPS

#ifdef GET_INSTRINFO_OPERAND_TYPES_ENUM
#undef GET_INSTRINFO_OPERAND_TYPES_ENUM
namespace llvm {namespace Mips {
namespace OpTypes { 
enum OperandType {
  InvertedImOperand = 0,
  InvertedImOperand64 = 1,
  LSAImm = 2,
  PtrRC = 3,
  brtarget = 4,
  brtarget21 = 5,
  brtarget26 = 6,
  brtarget7_mm = 7,
  brtarget_mm = 8,
  calloffset16 = 9,
  calltarget = 10,
  calltarget_mm = 11,
  condcode = 12,
  cpinst_operand = 13,
  f32imm = 14,
  f64imm = 15,
  i16imm = 16,
  i1imm = 17,
  i32imm = 18,
  i64imm = 19,
  i8imm = 20,
  imm32 = 21,
  imm64 = 22,
  jmpoffset16 = 23,
  jmptarget = 24,
  jmptarget_mm = 25,
  li_simm7 = 26,
  mem = 27,
  mem16 = 28,
  mem16_ea = 29,
  mem_ea = 30,
  mem_mm_12 = 31,
  mem_mm_4 = 32,
  mem_mm_4_lsl1 = 33,
  mem_mm_4_lsl2 = 34,
  mem_mm_4sp = 35,
  mem_mm_sp_imm5_lsl2 = 36,
  mem_msa = 37,
  mem_simm11 = 38,
  mem_simm16 = 39,
  mem_simm9 = 40,
  pcrel16 = 41,
  reglist = 42,
  reglist16 = 43,
  regpair = 44,
  simm10 = 45,
  simm10_64 = 46,
  simm11 = 47,
  simm12 = 48,
  simm16 = 49,
  simm16_64 = 50,
  simm18_lsl3 = 51,
  simm19_lsl2 = 52,
  simm20 = 53,
  simm3_lsa2 = 54,
  simm4 = 55,
  simm5 = 56,
  simm9 = 57,
  simm9_addiusp = 58,
  size_ext = 59,
  size_ins = 60,
  uimm10 = 61,
  uimm16 = 62,
  uimm16_64 = 63,
  uimm2 = 64,
  uimm20 = 65,
  uimm3 = 66,
  uimm3_shift = 67,
  uimm4 = 68,
  uimm4_andi = 69,
  uimm5 = 70,
  uimm5_lsl2 = 71,
  uimm6 = 72,
  uimm6_lsl2 = 73,
  uimm8 = 74,
  uimmz = 75,
  vsplat_simm10 = 76,
  vsplat_simm5 = 77,
  vsplat_uimm1 = 78,
  vsplat_uimm2 = 79,
  vsplat_uimm3 = 80,
  vsplat_uimm4 = 81,
  vsplat_uimm5 = 82,
  vsplat_uimm6 = 83,
  vsplat_uimm8 = 84,
  OPERAND_TYPE_LIST_END
};
} // End namespace OpTypes
} // End namespace Mips
} // End namespace llvm
#endif // GET_INSTRINFO_OPERAND_TYPES_ENUM
#ifdef GET_INSTRMAP_INFO
#undef GET_INSTRMAP_INFO
namespace llvm {

namespace Mips {

enum Arch {
	Arch_se,
	Arch_micromips
};

// Std2MicroMips
int Std2MicroMips(uint16_t Opcode, enum Arch inArch) {
static const uint16_t Std2MicroMipsTable[][3] = {
  { Mips::ADD, Mips::ADD, Mips::ADD_MM },
  { Mips::ADDi, Mips::ADDi, Mips::ADDi_MM },
  { Mips::ADDiu, Mips::ADDiu, Mips::ADDiu_MM },
  { Mips::ADDu, Mips::ADDu, Mips::ADDu_MM },
  { Mips::AND, Mips::AND, Mips::AND_MM },
  { Mips::ANDi, Mips::ANDi, Mips::ANDi_MM },
  { Mips::BC1F, Mips::BC1F, Mips::BC1F_MM },
  { Mips::BC1FL, Mips::BC1FL, (uint16_t)-1U },
  { Mips::BC1T, Mips::BC1T, Mips::BC1T_MM },
  { Mips::BC1TL, Mips::BC1TL, (uint16_t)-1U },
  { Mips::BEQ, Mips::BEQ, Mips::BEQ_MM },
  { Mips::BEQL, Mips::BEQL, (uint16_t)-1U },
  { Mips::BGEZ, Mips::BGEZ, Mips::BGEZ_MM },
  { Mips::BGEZAL, Mips::BGEZAL, Mips::BGEZAL_MM },
  { Mips::BGEZALL, Mips::BGEZALL, (uint16_t)-1U },
  { Mips::BGEZL, Mips::BGEZL, (uint16_t)-1U },
  { Mips::BGTZ, Mips::BGTZ, Mips::BGTZ_MM },
  { Mips::BGTZL, Mips::BGTZL, (uint16_t)-1U },
  { Mips::BLEZ, Mips::BLEZ, Mips::BLEZ_MM },
  { Mips::BLEZL, Mips::BLEZL, (uint16_t)-1U },
  { Mips::BLTZ, Mips::BLTZ, Mips::BLTZ_MM },
  { Mips::BLTZAL, Mips::BLTZAL, Mips::BLTZAL_MM },
  { Mips::BLTZALL, Mips::BLTZALL, (uint16_t)-1U },
  { Mips::BLTZL, Mips::BLTZL, (uint16_t)-1U },
  { Mips::BNE, Mips::BNE, Mips::BNE_MM },
  { Mips::BNEL, Mips::BNEL, (uint16_t)-1U },
  { Mips::BREAK, Mips::BREAK, Mips::BREAK_MM },
  { Mips::CACHE, Mips::CACHE, Mips::CACHE_MM },
  { Mips::CEIL_W_D32, Mips::CEIL_W_D32, Mips::CEIL_W_MM },
  { Mips::CEIL_W_S, Mips::CEIL_W_S, Mips::CEIL_W_S_MM },
  { Mips::CFC1, Mips::CFC1, Mips::CFC1_MM },
  { Mips::CLO, Mips::CLO, Mips::CLO_MM },
  { Mips::CLZ, Mips::CLZ, Mips::CLZ_MM },
  { Mips::CTC1, Mips::CTC1, Mips::CTC1_MM },
  { Mips::CVT_D32_S, Mips::CVT_D32_S, Mips::CVT_D_S_MM },
  { Mips::CVT_D32_W, Mips::CVT_D32_W, Mips::CVT_D32_W_MM },
  { Mips::CVT_L_D64, Mips::CVT_L_D64, Mips::CVT_L_D64_MM },
  { Mips::CVT_L_S, Mips::CVT_L_S, Mips::CVT_L_S_MM },
  { Mips::CVT_S_D32, Mips::CVT_S_D32, Mips::CVT_S_D32_MM },
  { Mips::CVT_S_W, Mips::CVT_S_W, Mips::CVT_S_W_MM },
  { Mips::CVT_W_D32, Mips::CVT_W_D32, Mips::CVT_W_MM },
  { Mips::CVT_W_S, Mips::CVT_W_S, Mips::CVT_W_S_MM },
  { Mips::DERET, Mips::DERET, Mips::DERET_MM },
  { Mips::DI, Mips::DI, Mips::DI_MM },
  { Mips::EHB, Mips::EHB, Mips::EHB_MM },
  { Mips::EI, Mips::EI, Mips::EI_MM },
  { Mips::ERET, Mips::ERET, Mips::ERET_MM },
  { Mips::EXT, Mips::EXT, Mips::EXT_MM },
  { Mips::FABS_D32, Mips::FABS_D32, Mips::FABS_MM },
  { Mips::FABS_S, Mips::FABS_S, Mips::FABS_S_MM },
  { Mips::FADD_D32, Mips::FADD_D32, Mips::FADD_MM },
  { Mips::FADD_S, Mips::FADD_S, Mips::FADD_S_MM },
  { Mips::FCMP_D32, Mips::FCMP_D32, Mips::FCMP_D32_MM },
  { Mips::FCMP_S32, Mips::FCMP_S32, Mips::FCMP_S32_MM },
  { Mips::FDIV_D32, Mips::FDIV_D32, Mips::FDIV_MM },
  { Mips::FDIV_S, Mips::FDIV_S, Mips::FDIV_S_MM },
  { Mips::FLOOR_W_D32, Mips::FLOOR_W_D32, Mips::FLOOR_W_MM },
  { Mips::FLOOR_W_S, Mips::FLOOR_W_S, Mips::FLOOR_W_S_MM },
  { Mips::FMOV_D32, Mips::FMOV_D32, Mips::FMOV_D32_MM },
  { Mips::FMOV_S, Mips::FMOV_S, Mips::FMOV_S_MM },
  { Mips::FMUL_D32, Mips::FMUL_D32, Mips::FMUL_MM },
  { Mips::FMUL_S, Mips::FMUL_S, Mips::FMUL_S_MM },
  { Mips::FNEG_D32, Mips::FNEG_D32, Mips::FNEG_MM },
  { Mips::FNEG_S, Mips::FNEG_S, Mips::FNEG_S_MM },
  { Mips::FSQRT_D32, Mips::FSQRT_D32, Mips::FSQRT_MM },
  { Mips::FSQRT_S, Mips::FSQRT_S, Mips::FSQRT_S_MM },
  { Mips::FSUB_D32, Mips::FSUB_D32, Mips::FSUB_MM },
  { Mips::FSUB_S, Mips::FSUB_S, Mips::FSUB_S_MM },
  { Mips::INS, Mips::INS, Mips::INS_MM },
  { Mips::J, Mips::J, Mips::J_MM },
  { Mips::JAL, Mips::JAL, Mips::JAL_MM },
  { Mips::JR, Mips::JR, Mips::JR_MM },
  { Mips::LB, Mips::LB, Mips::LB_MM },
  { Mips::LBu, Mips::LBu, Mips::LBu_MM },
  { Mips::LDC1, Mips::LDC1, Mips::LDC1_MM },
  { Mips::LEA_ADDiu, Mips::LEA_ADDiu, Mips::LEA_ADDiu_MM },
  { Mips::LH, Mips::LH, Mips::LH_MM },
  { Mips::LHu, Mips::LHu, Mips::LHu_MM },
  { Mips::LUXC1, Mips::LUXC1, Mips::LUXC1_MM },
  { Mips::LUi, Mips::LUi, Mips::LUi_MM },
  { Mips::LW, Mips::LW, Mips::LW_MM },
  { Mips::LWC1, Mips::LWC1, Mips::LWC1_MM },
  { Mips::LWXC1, Mips::LWXC1, Mips::LWXC1_MM },
  { Mips::MADD, Mips::MADD, Mips::MADD_MM },
  { Mips::MADDU, Mips::MADDU, Mips::MADDU_MM },
  { Mips::MADD_D32, Mips::MADD_D32, Mips::MADD_D32_MM },
  { Mips::MADD_S, Mips::MADD_S, Mips::MADD_S_MM },
  { Mips::MFC1, Mips::MFC1, Mips::MFC1_MM },
  { Mips::MFHC1_D32, Mips::MFHC1_D32, Mips::MFHC1_MM },
  { Mips::MFHI, Mips::MFHI, Mips::MFHI_MM },
  { Mips::MFLO, Mips::MFLO, Mips::MFLO_MM },
  { Mips::MOVF_D32, Mips::MOVF_D32, Mips::MOVF_D32_MM },
  { Mips::MOVF_I, Mips::MOVF_I, Mips::MOVF_I_MM },
  { Mips::MOVF_S, Mips::MOVF_S, Mips::MOVF_S_MM },
  { Mips::MOVN_I_D32, Mips::MOVN_I_D32, Mips::MOVN_I_D32_MM },
  { Mips::MOVN_I_I, Mips::MOVN_I_I, Mips::MOVN_I_MM },
  { Mips::MOVN_I_S, Mips::MOVN_I_S, Mips::MOVN_I_S_MM },
  { Mips::MOVT_D32, Mips::MOVT_D32, Mips::MOVT_D32_MM },
  { Mips::MOVT_I, Mips::MOVT_I, Mips::MOVT_I_MM },
  { Mips::MOVT_S, Mips::MOVT_S, Mips::MOVT_S_MM },
  { Mips::MOVZ_I_D32, Mips::MOVZ_I_D32, Mips::MOVZ_I_D32_MM },
  { Mips::MOVZ_I_I, Mips::MOVZ_I_I, Mips::MOVZ_I_MM },
  { Mips::MOVZ_I_S, Mips::MOVZ_I_S, Mips::MOVZ_I_S_MM },
  { Mips::MSUB, Mips::MSUB, Mips::MSUB_MM },
  { Mips::MSUBU, Mips::MSUBU, Mips::MSUBU_MM },
  { Mips::MSUB_D32, Mips::MSUB_D32, Mips::MSUB_D32_MM },
  { Mips::MSUB_S, Mips::MSUB_S, Mips::MSUB_S_MM },
  { Mips::MTC1, Mips::MTC1, Mips::MTC1_MM },
  { Mips::MTHC1_D32, Mips::MTHC1_D32, Mips::MTHC1_MM },
  { Mips::MTHI, Mips::MTHI, Mips::MTHI_MM },
  { Mips::MTLO, Mips::MTLO, Mips::MTLO_MM },
  { Mips::MUL, Mips::MUL, Mips::MUL_MM },
  { Mips::MULT, Mips::MULT, Mips::MULT_MM },
  { Mips::MULTu, Mips::MULTu, Mips::MULTu_MM },
  { Mips::NMADD_D32, Mips::NMADD_D32, Mips::NMADD_D32_MM },
  { Mips::NMADD_S, Mips::NMADD_S, Mips::NMADD_S_MM },
  { Mips::NMSUB_D32, Mips::NMSUB_D32, Mips::NMSUB_D32_MM },
  { Mips::NMSUB_S, Mips::NMSUB_S, Mips::NMSUB_S_MM },
  { Mips::NOR, Mips::NOR, Mips::NOR_MM },
  { Mips::OR, Mips::OR, Mips::OR_MM },
  { Mips::ORi, Mips::ORi, Mips::ORi_MM },
  { Mips::PAUSE, Mips::PAUSE, Mips::PAUSE_MM },
  { Mips::PREF, Mips::PREF, Mips::PREF_MM },
  { Mips::RDHWR, Mips::RDHWR, Mips::RDHWR_MM },
  { Mips::ROTR, Mips::ROTR, Mips::ROTR_MM },
  { Mips::ROTRV, Mips::ROTRV, Mips::ROTRV_MM },
  { Mips::ROUND_W_D32, Mips::ROUND_W_D32, Mips::ROUND_W_MM },
  { Mips::ROUND_W_S, Mips::ROUND_W_S, Mips::ROUND_W_S_MM },
  { Mips::SB, Mips::SB, Mips::SB_MM },
  { Mips::SDBBP, Mips::SDBBP, Mips::SDBBP_MM },
  { Mips::SDC1, Mips::SDC1, Mips::SDC1_MM },
  { Mips::SDIV, Mips::SDIV, Mips::SDIV_MM },
  { Mips::SEB, Mips::SEB, Mips::SEB_MM },
  { Mips::SEH, Mips::SEH, Mips::SEH_MM },
  { Mips::SH, Mips::SH, Mips::SH_MM },
  { Mips::SLL, Mips::SLL, Mips::SLL_MM },
  { Mips::SLLV, Mips::SLLV, Mips::SLLV_MM },
  { Mips::SLT, Mips::SLT, Mips::SLT_MM },
  { Mips::SLTi, Mips::SLTi, Mips::SLTi_MM },
  { Mips::SLTiu, Mips::SLTiu, Mips::SLTiu_MM },
  { Mips::SLTu, Mips::SLTu, Mips::SLTu_MM },
  { Mips::SRA, Mips::SRA, Mips::SRA_MM },
  { Mips::SRAV, Mips::SRAV, Mips::SRAV_MM },
  { Mips::SRL, Mips::SRL, Mips::SRL_MM },
  { Mips::SRLV, Mips::SRLV, Mips::SRLV_MM },
  { Mips::SSNOP, Mips::SSNOP, Mips::SSNOP_MM },
  { Mips::SUB, Mips::SUB, Mips::SUB_MM },
  { Mips::SUBu, Mips::SUBu, Mips::SUBu_MM },
  { Mips::SUXC1, Mips::SUXC1, Mips::SUXC1_MM },
  { Mips::SW, Mips::SW, Mips::SW_MM },
  { Mips::SWC1, Mips::SWC1, Mips::SWC1_MM },
  { Mips::SWXC1, Mips::SWXC1, Mips::SWXC1_MM },
  { Mips::SYNC, Mips::SYNC, Mips::SYNC_MM },
  { Mips::SYNCI, Mips::SYNCI, (uint16_t)-1U },
  { Mips::SYSCALL, Mips::SYSCALL, Mips::SYSCALL_MM },
  { Mips::TEQ, Mips::TEQ, Mips::TEQ_MM },
  { Mips::TEQI, Mips::TEQI, Mips::TEQI_MM },
  { Mips::TGE, Mips::TGE, Mips::TGE_MM },
  { Mips::TGEI, Mips::TGEI, Mips::TGEI_MM },
  { Mips::TGEIU, Mips::TGEIU, Mips::TGEIU_MM },
  { Mips::TGEU, Mips::TGEU, Mips::TGEU_MM },
  { Mips::TLBP, Mips::TLBP, Mips::TLBP_MM },
  { Mips::TLBR, Mips::TLBR, Mips::TLBR_MM },
  { Mips::TLBWI, Mips::TLBWI, Mips::TLBWI_MM },
  { Mips::TLBWR, Mips::TLBWR, Mips::TLBWR_MM },
  { Mips::TLT, Mips::TLT, Mips::TLT_MM },
  { Mips::TLTI, Mips::TLTI, Mips::TLTI_MM },
  { Mips::TLTU, Mips::TLTU, Mips::TLTU_MM },
  { Mips::TNE, Mips::TNE, Mips::TNE_MM },
  { Mips::TNEI, Mips::TNEI, Mips::TNEI_MM },
  { Mips::TRUNC_W_D32, Mips::TRUNC_W_D32, Mips::TRUNC_W_MM },
  { Mips::TRUNC_W_S, Mips::TRUNC_W_S, Mips::TRUNC_W_S_MM },
  { Mips::TTLTIU, Mips::TTLTIU, Mips::TLTIU_MM },
  { Mips::UDIV, Mips::UDIV, Mips::UDIV_MM },
  { Mips::WSBH, Mips::WSBH, Mips::WSBH_MM },
  { Mips::XOR, Mips::XOR, Mips::XOR_MM },
  { Mips::XORi, Mips::XORi, Mips::XORi_MM },
}; // End of Std2MicroMipsTable

  unsigned mid;
  unsigned start = 0;
  unsigned end = 177;
  while (start < end) {
    mid = start + (end - start)/2;
    if (Opcode == Std2MicroMipsTable[mid][0]) {
      break;
    }
    if (Opcode < Std2MicroMipsTable[mid][0])
      end = mid;
    else
      start = mid + 1;
  }
  if (start == end)
    return -1; // Instruction doesn't exist in this table.

  if (inArch == Arch_se)
    return Std2MicroMipsTable[mid][1];
  if (inArch == Arch_micromips)
    return Std2MicroMipsTable[mid][2];
  return -1;}

} // End Mips namespace
} // End llvm namespace
#endif // GET_INSTRMAP_INFO

