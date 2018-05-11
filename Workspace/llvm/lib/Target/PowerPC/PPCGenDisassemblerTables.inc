/*===- TableGen'erated file -------------------------------------*- C++ -*-===*\
|*                                                                            *|
|* * PPC Disassembler                                                         *|
|*                                                                            *|
|* Automatically generated file, do not edit!                                 *|
|*                                                                            *|
\*===----------------------------------------------------------------------===*/

#include "llvm/MC/MCInst.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/LEB128.h"
#include "llvm/Support/raw_ostream.h"
#include <assert.h>

namespace llvm {

// Helper function for extracting fields from encoded instructions.
template<typename InsnType>
static InsnType fieldFromInstruction(InsnType insn, unsigned startBit,
                                     unsigned numBits) {
    assert(startBit + numBits <= (sizeof(InsnType)*8) &&
           "Instruction field out of bounds!");
    InsnType fieldMask;
    if (numBits == sizeof(InsnType)*8)
      fieldMask = (InsnType)(-1LL);
    else
      fieldMask = (((InsnType)1 << numBits) - 1) << startBit;
    return (insn & fieldMask) >> startBit;
}

static const uint8_t DecoderTable32[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 17
/* 7 */       MCD::OPC_CheckField, 1, 10, 128, 2, 41, 37, // Skip to: 9527
/* 14 */      MCD::OPC_Decode, 115, 0, // Opcode: ATTN
/* 17 */      MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 25
/* 21 */      MCD::OPC_Decode, 189, 7, 1, // Opcode: TDI
/* 25 */      MCD::OPC_FilterValue, 3, 4, 0, // Skip to: 33
/* 29 */      MCD::OPC_Decode, 206, 7, 2, // Opcode: TWI
/* 33 */      MCD::OPC_FilterValue, 4, 155, 5, // Skip to: 1472
/* 37 */      MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 40 */      MCD::OPC_FilterValue, 0, 163, 0, // Skip to: 207
/* 44 */      MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 47 */      MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 55
/* 51 */      MCD::OPC_Decode, 214, 7, 3, // Opcode: VADDUBM
/* 55 */      MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 63
/* 59 */      MCD::OPC_Decode, 216, 7, 3, // Opcode: VADDUHM
/* 63 */      MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 71
/* 67 */      MCD::OPC_Decode, 218, 7, 3, // Opcode: VADDUWM
/* 71 */      MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 79
/* 75 */      MCD::OPC_Decode, 209, 7, 3, // Opcode: VADDCUW
/* 79 */      MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 87
/* 83 */      MCD::OPC_Decode, 215, 7, 3, // Opcode: VADDUBS
/* 87 */      MCD::OPC_FilterValue, 9, 4, 0, // Skip to: 95
/* 91 */      MCD::OPC_Decode, 217, 7, 3, // Opcode: VADDUHS
/* 95 */      MCD::OPC_FilterValue, 10, 4, 0, // Skip to: 103
/* 99 */      MCD::OPC_Decode, 219, 7, 3, // Opcode: VADDUWS
/* 103 */     MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 111
/* 107 */     MCD::OPC_Decode, 211, 7, 3, // Opcode: VADDSBS
/* 111 */     MCD::OPC_FilterValue, 13, 4, 0, // Skip to: 119
/* 115 */     MCD::OPC_Decode, 212, 7, 3, // Opcode: VADDSHS
/* 119 */     MCD::OPC_FilterValue, 14, 4, 0, // Skip to: 127
/* 123 */     MCD::OPC_Decode, 213, 7, 3, // Opcode: VADDSWS
/* 127 */     MCD::OPC_FilterValue, 16, 4, 0, // Skip to: 135
/* 131 */     MCD::OPC_Decode, 222, 8, 3, // Opcode: VSUBUBM
/* 135 */     MCD::OPC_FilterValue, 17, 4, 0, // Skip to: 143
/* 139 */     MCD::OPC_Decode, 224, 8, 3, // Opcode: VSUBUHM
/* 143 */     MCD::OPC_FilterValue, 18, 4, 0, // Skip to: 151
/* 147 */     MCD::OPC_Decode, 226, 8, 3, // Opcode: VSUBUWM
/* 151 */     MCD::OPC_FilterValue, 22, 4, 0, // Skip to: 159
/* 155 */     MCD::OPC_Decode, 217, 8, 3, // Opcode: VSUBCUW
/* 159 */     MCD::OPC_FilterValue, 24, 4, 0, // Skip to: 167
/* 163 */     MCD::OPC_Decode, 223, 8, 3, // Opcode: VSUBUBS
/* 167 */     MCD::OPC_FilterValue, 25, 4, 0, // Skip to: 175
/* 171 */     MCD::OPC_Decode, 225, 8, 3, // Opcode: VSUBUHS
/* 175 */     MCD::OPC_FilterValue, 26, 4, 0, // Skip to: 183
/* 179 */     MCD::OPC_Decode, 227, 8, 3, // Opcode: VSUBUWS
/* 183 */     MCD::OPC_FilterValue, 28, 4, 0, // Skip to: 191
/* 187 */     MCD::OPC_Decode, 219, 8, 3, // Opcode: VSUBSBS
/* 191 */     MCD::OPC_FilterValue, 29, 4, 0, // Skip to: 199
/* 195 */     MCD::OPC_Decode, 220, 8, 3, // Opcode: VSUBSHS
/* 199 */     MCD::OPC_FilterValue, 30, 108, 36, // Skip to: 9527
/* 203 */     MCD::OPC_Decode, 221, 8, 3, // Opcode: VSUBSWS
/* 207 */     MCD::OPC_FilterValue, 2, 147, 0, // Skip to: 358
/* 211 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 214 */     MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 222
/* 218 */     MCD::OPC_Decode, 141, 8, 3, // Opcode: VMAXUB
/* 222 */     MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 230
/* 226 */     MCD::OPC_Decode, 142, 8, 3, // Opcode: VMAXUH
/* 230 */     MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 238
/* 234 */     MCD::OPC_Decode, 143, 8, 3, // Opcode: VMAXUW
/* 238 */     MCD::OPC_FilterValue, 4, 4, 0, // Skip to: 246
/* 242 */     MCD::OPC_Decode, 138, 8, 3, // Opcode: VMAXSB
/* 246 */     MCD::OPC_FilterValue, 5, 4, 0, // Skip to: 254
/* 250 */     MCD::OPC_Decode, 139, 8, 3, // Opcode: VMAXSH
/* 254 */     MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 262
/* 258 */     MCD::OPC_Decode, 140, 8, 3, // Opcode: VMAXSW
/* 262 */     MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 270
/* 266 */     MCD::OPC_Decode, 150, 8, 3, // Opcode: VMINUB
/* 270 */     MCD::OPC_FilterValue, 9, 4, 0, // Skip to: 278
/* 274 */     MCD::OPC_Decode, 151, 8, 3, // Opcode: VMINUH
/* 278 */     MCD::OPC_FilterValue, 10, 4, 0, // Skip to: 286
/* 282 */     MCD::OPC_Decode, 152, 8, 3, // Opcode: VMINUW
/* 286 */     MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 294
/* 290 */     MCD::OPC_Decode, 147, 8, 3, // Opcode: VMINSB
/* 294 */     MCD::OPC_FilterValue, 13, 4, 0, // Skip to: 302
/* 298 */     MCD::OPC_Decode, 148, 8, 3, // Opcode: VMINSH
/* 302 */     MCD::OPC_FilterValue, 14, 4, 0, // Skip to: 310
/* 306 */     MCD::OPC_Decode, 149, 8, 3, // Opcode: VMINSW
/* 310 */     MCD::OPC_FilterValue, 16, 4, 0, // Skip to: 318
/* 314 */     MCD::OPC_Decode, 225, 7, 3, // Opcode: VAVGUB
/* 318 */     MCD::OPC_FilterValue, 17, 4, 0, // Skip to: 326
/* 322 */     MCD::OPC_Decode, 226, 7, 3, // Opcode: VAVGUH
/* 326 */     MCD::OPC_FilterValue, 18, 4, 0, // Skip to: 334
/* 330 */     MCD::OPC_Decode, 227, 7, 3, // Opcode: VAVGUW
/* 334 */     MCD::OPC_FilterValue, 20, 4, 0, // Skip to: 342
/* 338 */     MCD::OPC_Decode, 222, 7, 3, // Opcode: VAVGSB
/* 342 */     MCD::OPC_FilterValue, 21, 4, 0, // Skip to: 350
/* 346 */     MCD::OPC_Decode, 223, 7, 3, // Opcode: VAVGSH
/* 350 */     MCD::OPC_FilterValue, 22, 213, 35, // Skip to: 9527
/* 354 */     MCD::OPC_Decode, 224, 7, 3, // Opcode: VAVGSW
/* 358 */     MCD::OPC_FilterValue, 4, 183, 0, // Skip to: 545
/* 362 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 365 */     MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 373
/* 369 */     MCD::OPC_Decode, 192, 8, 3, // Opcode: VRLB
/* 373 */     MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 381
/* 377 */     MCD::OPC_Decode, 193, 8, 3, // Opcode: VRLH
/* 381 */     MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 389
/* 385 */     MCD::OPC_Decode, 194, 8, 3, // Opcode: VRLW
/* 389 */     MCD::OPC_FilterValue, 4, 4, 0, // Skip to: 397
/* 393 */     MCD::OPC_Decode, 198, 8, 3, // Opcode: VSLB
/* 397 */     MCD::OPC_FilterValue, 5, 4, 0, // Skip to: 405
/* 401 */     MCD::OPC_Decode, 200, 8, 3, // Opcode: VSLH
/* 405 */     MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 413
/* 409 */     MCD::OPC_Decode, 202, 8, 3, // Opcode: VSLW
/* 413 */     MCD::OPC_FilterValue, 7, 4, 0, // Skip to: 421
/* 417 */     MCD::OPC_Decode, 197, 8, 3, // Opcode: VSL
/* 421 */     MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 429
/* 425 */     MCD::OPC_Decode, 213, 8, 3, // Opcode: VSRB
/* 429 */     MCD::OPC_FilterValue, 9, 4, 0, // Skip to: 437
/* 433 */     MCD::OPC_Decode, 214, 8, 3, // Opcode: VSRH
/* 437 */     MCD::OPC_FilterValue, 10, 4, 0, // Skip to: 445
/* 441 */     MCD::OPC_Decode, 216, 8, 3, // Opcode: VSRW
/* 445 */     MCD::OPC_FilterValue, 11, 4, 0, // Skip to: 453
/* 449 */     MCD::OPC_Decode, 209, 8, 3, // Opcode: VSR
/* 453 */     MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 461
/* 457 */     MCD::OPC_Decode, 210, 8, 3, // Opcode: VSRAB
/* 461 */     MCD::OPC_FilterValue, 13, 4, 0, // Skip to: 469
/* 465 */     MCD::OPC_Decode, 211, 8, 3, // Opcode: VSRAH
/* 469 */     MCD::OPC_FilterValue, 14, 4, 0, // Skip to: 477
/* 473 */     MCD::OPC_Decode, 212, 8, 3, // Opcode: VSRAW
/* 477 */     MCD::OPC_FilterValue, 16, 4, 0, // Skip to: 485
/* 481 */     MCD::OPC_Decode, 220, 7, 3, // Opcode: VAND
/* 485 */     MCD::OPC_FilterValue, 17, 4, 0, // Skip to: 493
/* 489 */     MCD::OPC_Decode, 221, 7, 3, // Opcode: VANDC
/* 493 */     MCD::OPC_FilterValue, 18, 4, 0, // Skip to: 501
/* 497 */     MCD::OPC_Decode, 176, 8, 3, // Opcode: VOR
/* 501 */     MCD::OPC_FilterValue, 19, 4, 0, // Skip to: 509
/* 505 */     MCD::OPC_Decode, 239, 8, 3, // Opcode: VXOR
/* 509 */     MCD::OPC_FilterValue, 20, 4, 0, // Skip to: 517
/* 513 */     MCD::OPC_Decode, 175, 8, 3, // Opcode: VNOR
/* 517 */     MCD::OPC_FilterValue, 24, 10, 0, // Skip to: 531
/* 521 */     MCD::OPC_CheckField, 11, 10, 0, 40, 35, // Skip to: 9527
/* 527 */     MCD::OPC_Decode, 189, 5, 4, // Opcode: MFVSCR
/* 531 */     MCD::OPC_FilterValue, 25, 32, 35, // Skip to: 9527
/* 535 */     MCD::OPC_CheckField, 16, 10, 0, 26, 35, // Skip to: 9527
/* 541 */     MCD::OPC_Decode, 212, 5, 5, // Opcode: MTVSCR
/* 545 */     MCD::OPC_FilterValue, 6, 211, 0, // Skip to: 760
/* 549 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 552 */     MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 560
/* 556 */     MCD::OPC_Decode, 236, 7, 3, // Opcode: VCMPEQUB
/* 560 */     MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 568
/* 564 */     MCD::OPC_Decode, 238, 7, 3, // Opcode: VCMPEQUH
/* 568 */     MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 576
/* 572 */     MCD::OPC_Decode, 240, 7, 3, // Opcode: VCMPEQUW
/* 576 */     MCD::OPC_FilterValue, 3, 4, 0, // Skip to: 584
/* 580 */     MCD::OPC_Decode, 234, 7, 3, // Opcode: VCMPEQFP
/* 584 */     MCD::OPC_FilterValue, 7, 4, 0, // Skip to: 592
/* 588 */     MCD::OPC_Decode, 242, 7, 3, // Opcode: VCMPGEFP
/* 592 */     MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 600
/* 596 */     MCD::OPC_Decode, 252, 7, 3, // Opcode: VCMPGTUB
/* 600 */     MCD::OPC_FilterValue, 9, 4, 0, // Skip to: 608
/* 604 */     MCD::OPC_Decode, 254, 7, 3, // Opcode: VCMPGTUH
/* 608 */     MCD::OPC_FilterValue, 10, 4, 0, // Skip to: 616
/* 612 */     MCD::OPC_Decode, 128, 8, 3, // Opcode: VCMPGTUW
/* 616 */     MCD::OPC_FilterValue, 11, 4, 0, // Skip to: 624
/* 620 */     MCD::OPC_Decode, 244, 7, 3, // Opcode: VCMPGTFP
/* 624 */     MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 632
/* 628 */     MCD::OPC_Decode, 246, 7, 3, // Opcode: VCMPGTSB
/* 632 */     MCD::OPC_FilterValue, 13, 4, 0, // Skip to: 640
/* 636 */     MCD::OPC_Decode, 248, 7, 3, // Opcode: VCMPGTSH
/* 640 */     MCD::OPC_FilterValue, 14, 4, 0, // Skip to: 648
/* 644 */     MCD::OPC_Decode, 250, 7, 3, // Opcode: VCMPGTSW
/* 648 */     MCD::OPC_FilterValue, 15, 4, 0, // Skip to: 656
/* 652 */     MCD::OPC_Decode, 232, 7, 3, // Opcode: VCMPBFP
/* 656 */     MCD::OPC_FilterValue, 16, 4, 0, // Skip to: 664
/* 660 */     MCD::OPC_Decode, 237, 7, 3, // Opcode: VCMPEQUBo
/* 664 */     MCD::OPC_FilterValue, 17, 4, 0, // Skip to: 672
/* 668 */     MCD::OPC_Decode, 239, 7, 3, // Opcode: VCMPEQUHo
/* 672 */     MCD::OPC_FilterValue, 18, 4, 0, // Skip to: 680
/* 676 */     MCD::OPC_Decode, 241, 7, 3, // Opcode: VCMPEQUWo
/* 680 */     MCD::OPC_FilterValue, 19, 4, 0, // Skip to: 688
/* 684 */     MCD::OPC_Decode, 235, 7, 3, // Opcode: VCMPEQFPo
/* 688 */     MCD::OPC_FilterValue, 23, 4, 0, // Skip to: 696
/* 692 */     MCD::OPC_Decode, 243, 7, 3, // Opcode: VCMPGEFPo
/* 696 */     MCD::OPC_FilterValue, 24, 4, 0, // Skip to: 704
/* 700 */     MCD::OPC_Decode, 253, 7, 3, // Opcode: VCMPGTUBo
/* 704 */     MCD::OPC_FilterValue, 25, 4, 0, // Skip to: 712
/* 708 */     MCD::OPC_Decode, 255, 7, 3, // Opcode: VCMPGTUHo
/* 712 */     MCD::OPC_FilterValue, 26, 4, 0, // Skip to: 720
/* 716 */     MCD::OPC_Decode, 129, 8, 3, // Opcode: VCMPGTUWo
/* 720 */     MCD::OPC_FilterValue, 27, 4, 0, // Skip to: 728
/* 724 */     MCD::OPC_Decode, 245, 7, 3, // Opcode: VCMPGTFPo
/* 728 */     MCD::OPC_FilterValue, 28, 4, 0, // Skip to: 736
/* 732 */     MCD::OPC_Decode, 247, 7, 3, // Opcode: VCMPGTSBo
/* 736 */     MCD::OPC_FilterValue, 29, 4, 0, // Skip to: 744
/* 740 */     MCD::OPC_Decode, 249, 7, 3, // Opcode: VCMPGTSHo
/* 744 */     MCD::OPC_FilterValue, 30, 4, 0, // Skip to: 752
/* 748 */     MCD::OPC_Decode, 251, 7, 3, // Opcode: VCMPGTSWo
/* 752 */     MCD::OPC_FilterValue, 31, 67, 34, // Skip to: 9527
/* 756 */     MCD::OPC_Decode, 233, 7, 3, // Opcode: VCMPBFPo
/* 760 */     MCD::OPC_FilterValue, 8, 107, 0, // Skip to: 871
/* 764 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 767 */     MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 775
/* 771 */     MCD::OPC_Decode, 172, 8, 3, // Opcode: VMULOUB
/* 775 */     MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 783
/* 779 */     MCD::OPC_Decode, 173, 8, 3, // Opcode: VMULOUH
/* 783 */     MCD::OPC_FilterValue, 4, 4, 0, // Skip to: 791
/* 787 */     MCD::OPC_Decode, 170, 8, 3, // Opcode: VMULOSB
/* 791 */     MCD::OPC_FilterValue, 5, 4, 0, // Skip to: 799
/* 795 */     MCD::OPC_Decode, 171, 8, 3, // Opcode: VMULOSH
/* 799 */     MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 807
/* 803 */     MCD::OPC_Decode, 168, 8, 3, // Opcode: VMULEUB
/* 807 */     MCD::OPC_FilterValue, 9, 4, 0, // Skip to: 815
/* 811 */     MCD::OPC_Decode, 169, 8, 3, // Opcode: VMULEUH
/* 815 */     MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 823
/* 819 */     MCD::OPC_Decode, 166, 8, 3, // Opcode: VMULESB
/* 823 */     MCD::OPC_FilterValue, 13, 4, 0, // Skip to: 831
/* 827 */     MCD::OPC_Decode, 167, 8, 3, // Opcode: VMULESH
/* 831 */     MCD::OPC_FilterValue, 24, 4, 0, // Skip to: 839
/* 835 */     MCD::OPC_Decode, 231, 8, 3, // Opcode: VSUM4UBS
/* 839 */     MCD::OPC_FilterValue, 25, 4, 0, // Skip to: 847
/* 843 */     MCD::OPC_Decode, 230, 8, 3, // Opcode: VSUM4SHS
/* 847 */     MCD::OPC_FilterValue, 26, 4, 0, // Skip to: 855
/* 851 */     MCD::OPC_Decode, 228, 8, 3, // Opcode: VSUM2SWS
/* 855 */     MCD::OPC_FilterValue, 28, 4, 0, // Skip to: 863
/* 859 */     MCD::OPC_Decode, 229, 8, 3, // Opcode: VSUM4SBS
/* 863 */     MCD::OPC_FilterValue, 30, 212, 33, // Skip to: 9527
/* 867 */     MCD::OPC_Decode, 232, 8, 3, // Opcode: VSUMSWS
/* 871 */     MCD::OPC_FilterValue, 10, 179, 0, // Skip to: 1054
/* 875 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 878 */     MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 886
/* 882 */     MCD::OPC_Decode, 210, 7, 3, // Opcode: VADDFP
/* 886 */     MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 894
/* 890 */     MCD::OPC_Decode, 218, 8, 3, // Opcode: VSUBFP
/* 894 */     MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 908
/* 898 */     MCD::OPC_CheckField, 16, 5, 0, 175, 33, // Skip to: 9527
/* 904 */     MCD::OPC_Decode, 187, 8, 6, // Opcode: VREFP
/* 908 */     MCD::OPC_FilterValue, 5, 10, 0, // Skip to: 922
/* 912 */     MCD::OPC_CheckField, 16, 5, 0, 161, 33, // Skip to: 9527
/* 918 */     MCD::OPC_Decode, 195, 8, 6, // Opcode: VRSQRTEFP
/* 922 */     MCD::OPC_FilterValue, 6, 10, 0, // Skip to: 936
/* 926 */     MCD::OPC_CheckField, 16, 5, 0, 147, 33, // Skip to: 9527
/* 932 */     MCD::OPC_Decode, 134, 8, 6, // Opcode: VEXPTEFP
/* 936 */     MCD::OPC_FilterValue, 7, 10, 0, // Skip to: 950
/* 940 */     MCD::OPC_CheckField, 16, 5, 0, 133, 33, // Skip to: 9527
/* 946 */     MCD::OPC_Decode, 135, 8, 6, // Opcode: VLOGEFP
/* 950 */     MCD::OPC_FilterValue, 8, 10, 0, // Skip to: 964
/* 954 */     MCD::OPC_CheckField, 16, 5, 0, 119, 33, // Skip to: 9527
/* 960 */     MCD::OPC_Decode, 189, 8, 6, // Opcode: VRFIN
/* 964 */     MCD::OPC_FilterValue, 9, 10, 0, // Skip to: 978
/* 968 */     MCD::OPC_CheckField, 16, 5, 0, 105, 33, // Skip to: 9527
/* 974 */     MCD::OPC_Decode, 191, 8, 6, // Opcode: VRFIZ
/* 978 */     MCD::OPC_FilterValue, 10, 10, 0, // Skip to: 992
/* 982 */     MCD::OPC_CheckField, 16, 5, 0, 91, 33, // Skip to: 9527
/* 988 */     MCD::OPC_Decode, 190, 8, 6, // Opcode: VRFIP
/* 992 */     MCD::OPC_FilterValue, 11, 10, 0, // Skip to: 1006
/* 996 */     MCD::OPC_CheckField, 16, 5, 0, 77, 33, // Skip to: 9527
/* 1002 */    MCD::OPC_Decode, 188, 8, 6, // Opcode: VRFIM
/* 1006 */    MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 1014
/* 1010 */    MCD::OPC_Decode, 230, 7, 7, // Opcode: VCFUX
/* 1014 */    MCD::OPC_FilterValue, 13, 4, 0, // Skip to: 1022
/* 1018 */    MCD::OPC_Decode, 228, 7, 7, // Opcode: VCFSX
/* 1022 */    MCD::OPC_FilterValue, 14, 4, 0, // Skip to: 1030
/* 1026 */    MCD::OPC_Decode, 132, 8, 7, // Opcode: VCTUXS
/* 1030 */    MCD::OPC_FilterValue, 15, 4, 0, // Skip to: 1038
/* 1034 */    MCD::OPC_Decode, 130, 8, 7, // Opcode: VCTSXS
/* 1038 */    MCD::OPC_FilterValue, 16, 4, 0, // Skip to: 1046
/* 1042 */    MCD::OPC_Decode, 137, 8, 3, // Opcode: VMAXFP
/* 1046 */    MCD::OPC_FilterValue, 17, 29, 33, // Skip to: 9527
/* 1050 */    MCD::OPC_Decode, 146, 8, 3, // Opcode: VMINFP
/* 1054 */    MCD::OPC_FilterValue, 12, 133, 0, // Skip to: 1191
/* 1058 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 1061 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 1069
/* 1065 */    MCD::OPC_Decode, 154, 8, 3, // Opcode: VMRGHB
/* 1069 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 1077
/* 1073 */    MCD::OPC_Decode, 155, 8, 3, // Opcode: VMRGHH
/* 1077 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 1085
/* 1081 */    MCD::OPC_Decode, 156, 8, 3, // Opcode: VMRGHW
/* 1085 */    MCD::OPC_FilterValue, 4, 4, 0, // Skip to: 1093
/* 1089 */    MCD::OPC_Decode, 157, 8, 3, // Opcode: VMRGLB
/* 1093 */    MCD::OPC_FilterValue, 5, 4, 0, // Skip to: 1101
/* 1097 */    MCD::OPC_Decode, 158, 8, 3, // Opcode: VMRGLH
/* 1101 */    MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 1109
/* 1105 */    MCD::OPC_Decode, 159, 8, 3, // Opcode: VMRGLW
/* 1109 */    MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 1117
/* 1113 */    MCD::OPC_Decode, 203, 8, 7, // Opcode: VSPLTB
/* 1117 */    MCD::OPC_FilterValue, 9, 4, 0, // Skip to: 1125
/* 1121 */    MCD::OPC_Decode, 204, 8, 7, // Opcode: VSPLTH
/* 1125 */    MCD::OPC_FilterValue, 10, 4, 0, // Skip to: 1133
/* 1129 */    MCD::OPC_Decode, 208, 8, 7, // Opcode: VSPLTW
/* 1133 */    MCD::OPC_FilterValue, 12, 10, 0, // Skip to: 1147
/* 1137 */    MCD::OPC_CheckField, 11, 5, 0, 192, 32, // Skip to: 9527
/* 1143 */    MCD::OPC_Decode, 205, 8, 8, // Opcode: VSPLTISB
/* 1147 */    MCD::OPC_FilterValue, 13, 10, 0, // Skip to: 1161
/* 1151 */    MCD::OPC_CheckField, 11, 5, 0, 178, 32, // Skip to: 9527
/* 1157 */    MCD::OPC_Decode, 206, 8, 8, // Opcode: VSPLTISH
/* 1161 */    MCD::OPC_FilterValue, 14, 10, 0, // Skip to: 1175
/* 1165 */    MCD::OPC_CheckField, 11, 5, 0, 164, 32, // Skip to: 9527
/* 1171 */    MCD::OPC_Decode, 207, 8, 8, // Opcode: VSPLTISW
/* 1175 */    MCD::OPC_FilterValue, 16, 4, 0, // Skip to: 1183
/* 1179 */    MCD::OPC_Decode, 201, 8, 3, // Opcode: VSLO
/* 1183 */    MCD::OPC_FilterValue, 17, 148, 32, // Skip to: 9527
/* 1187 */    MCD::OPC_Decode, 215, 8, 3, // Opcode: VSRO
/* 1191 */    MCD::OPC_FilterValue, 14, 159, 0, // Skip to: 1354
/* 1195 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 1198 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 1206
/* 1202 */    MCD::OPC_Decode, 183, 8, 3, // Opcode: VPKUHUM
/* 1206 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 1214
/* 1210 */    MCD::OPC_Decode, 185, 8, 3, // Opcode: VPKUWUM
/* 1214 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 1222
/* 1218 */    MCD::OPC_Decode, 184, 8, 3, // Opcode: VPKUHUS
/* 1222 */    MCD::OPC_FilterValue, 3, 4, 0, // Skip to: 1230
/* 1226 */    MCD::OPC_Decode, 186, 8, 3, // Opcode: VPKUWUS
/* 1230 */    MCD::OPC_FilterValue, 4, 4, 0, // Skip to: 1238
/* 1234 */    MCD::OPC_Decode, 180, 8, 3, // Opcode: VPKSHUS
/* 1238 */    MCD::OPC_FilterValue, 5, 4, 0, // Skip to: 1246
/* 1242 */    MCD::OPC_Decode, 182, 8, 3, // Opcode: VPKSWUS
/* 1246 */    MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 1254
/* 1250 */    MCD::OPC_Decode, 179, 8, 3, // Opcode: VPKSHSS
/* 1254 */    MCD::OPC_FilterValue, 7, 4, 0, // Skip to: 1262
/* 1258 */    MCD::OPC_Decode, 181, 8, 3, // Opcode: VPKSWSS
/* 1262 */    MCD::OPC_FilterValue, 8, 10, 0, // Skip to: 1276
/* 1266 */    MCD::OPC_CheckField, 16, 5, 0, 63, 32, // Skip to: 9527
/* 1272 */    MCD::OPC_Decode, 234, 8, 6, // Opcode: VUPKHSB
/* 1276 */    MCD::OPC_FilterValue, 9, 10, 0, // Skip to: 1290
/* 1280 */    MCD::OPC_CheckField, 16, 5, 0, 49, 32, // Skip to: 9527
/* 1286 */    MCD::OPC_Decode, 235, 8, 6, // Opcode: VUPKHSH
/* 1290 */    MCD::OPC_FilterValue, 10, 10, 0, // Skip to: 1304
/* 1294 */    MCD::OPC_CheckField, 16, 5, 0, 35, 32, // Skip to: 9527
/* 1300 */    MCD::OPC_Decode, 237, 8, 6, // Opcode: VUPKLSB
/* 1304 */    MCD::OPC_FilterValue, 11, 10, 0, // Skip to: 1318
/* 1308 */    MCD::OPC_CheckField, 16, 5, 0, 21, 32, // Skip to: 9527
/* 1314 */    MCD::OPC_Decode, 238, 8, 6, // Opcode: VUPKLSH
/* 1318 */    MCD::OPC_FilterValue, 12, 4, 0, // Skip to: 1326
/* 1322 */    MCD::OPC_Decode, 178, 8, 3, // Opcode: VPKPX
/* 1326 */    MCD::OPC_FilterValue, 13, 10, 0, // Skip to: 1340
/* 1330 */    MCD::OPC_CheckField, 16, 5, 0, 255, 31, // Skip to: 9527
/* 1336 */    MCD::OPC_Decode, 233, 8, 6, // Opcode: VUPKHPX
/* 1340 */    MCD::OPC_FilterValue, 15, 247, 31, // Skip to: 9527
/* 1344 */    MCD::OPC_CheckField, 16, 5, 0, 241, 31, // Skip to: 9527
/* 1350 */    MCD::OPC_Decode, 236, 8, 6, // Opcode: VUPKLPX
/* 1354 */    MCD::OPC_FilterValue, 32, 4, 0, // Skip to: 1362
/* 1358 */    MCD::OPC_Decode, 144, 8, 9, // Opcode: VMHADDSHS
/* 1362 */    MCD::OPC_FilterValue, 33, 4, 0, // Skip to: 1370
/* 1366 */    MCD::OPC_Decode, 145, 8, 9, // Opcode: VMHRADDSHS
/* 1370 */    MCD::OPC_FilterValue, 34, 4, 0, // Skip to: 1378
/* 1374 */    MCD::OPC_Decode, 153, 8, 9, // Opcode: VMLADDUHM
/* 1378 */    MCD::OPC_FilterValue, 36, 4, 0, // Skip to: 1386
/* 1382 */    MCD::OPC_Decode, 163, 8, 9, // Opcode: VMSUMUBM
/* 1386 */    MCD::OPC_FilterValue, 37, 4, 0, // Skip to: 1394
/* 1390 */    MCD::OPC_Decode, 160, 8, 9, // Opcode: VMSUMMBM
/* 1394 */    MCD::OPC_FilterValue, 38, 4, 0, // Skip to: 1402
/* 1398 */    MCD::OPC_Decode, 164, 8, 9, // Opcode: VMSUMUHM
/* 1402 */    MCD::OPC_FilterValue, 39, 4, 0, // Skip to: 1410
/* 1406 */    MCD::OPC_Decode, 165, 8, 9, // Opcode: VMSUMUHS
/* 1410 */    MCD::OPC_FilterValue, 40, 4, 0, // Skip to: 1418
/* 1414 */    MCD::OPC_Decode, 161, 8, 9, // Opcode: VMSUMSHM
/* 1418 */    MCD::OPC_FilterValue, 41, 4, 0, // Skip to: 1426
/* 1422 */    MCD::OPC_Decode, 162, 8, 9, // Opcode: VMSUMSHS
/* 1426 */    MCD::OPC_FilterValue, 42, 4, 0, // Skip to: 1434
/* 1430 */    MCD::OPC_Decode, 196, 8, 9, // Opcode: VSEL
/* 1434 */    MCD::OPC_FilterValue, 43, 4, 0, // Skip to: 1442
/* 1438 */    MCD::OPC_Decode, 177, 8, 9, // Opcode: VPERM
/* 1442 */    MCD::OPC_FilterValue, 44, 10, 0, // Skip to: 1456
/* 1446 */    MCD::OPC_CheckField, 10, 1, 0, 139, 31, // Skip to: 9527
/* 1452 */    MCD::OPC_Decode, 199, 8, 10, // Opcode: VSLDOI
/* 1456 */    MCD::OPC_FilterValue, 46, 4, 0, // Skip to: 1464
/* 1460 */    MCD::OPC_Decode, 136, 8, 11, // Opcode: VMADDFP
/* 1464 */    MCD::OPC_FilterValue, 47, 123, 31, // Skip to: 9527
/* 1468 */    MCD::OPC_Decode, 174, 8, 11, // Opcode: VNMSUBFP
/* 1472 */    MCD::OPC_FilterValue, 7, 4, 0, // Skip to: 1480
/* 1476 */    MCD::OPC_Decode, 223, 5, 12, // Opcode: MULLI
/* 1480 */    MCD::OPC_FilterValue, 8, 4, 0, // Skip to: 1488
/* 1484 */    MCD::OPC_Decode, 160, 7, 12, // Opcode: SUBFIC
/* 1488 */    MCD::OPC_FilterValue, 10, 19, 0, // Skip to: 1511
/* 1492 */    MCD::OPC_ExtractField, 21, 2,  // Inst{22-21} ...
/* 1495 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 1503
/* 1499 */    MCD::OPC_Decode, 219, 1, 13, // Opcode: CMPLWI
/* 1503 */    MCD::OPC_FilterValue, 1, 84, 31, // Skip to: 9527
/* 1507 */    MCD::OPC_Decode, 217, 1, 14, // Opcode: CMPLDI
/* 1511 */    MCD::OPC_FilterValue, 11, 19, 0, // Skip to: 1534
/* 1515 */    MCD::OPC_ExtractField, 21, 2,  // Inst{22-21} ...
/* 1518 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 1526
/* 1522 */    MCD::OPC_Decode, 221, 1, 15, // Opcode: CMPWI
/* 1526 */    MCD::OPC_FilterValue, 1, 61, 31, // Skip to: 9527
/* 1530 */    MCD::OPC_Decode, 215, 1, 16, // Opcode: CMPDI
/* 1534 */    MCD::OPC_FilterValue, 12, 3, 0, // Skip to: 1541
/* 1538 */    MCD::OPC_Decode, 39, 12, // Opcode: ADDIC
/* 1541 */    MCD::OPC_FilterValue, 13, 3, 0, // Skip to: 1548
/* 1545 */    MCD::OPC_Decode, 41, 12, // Opcode: ADDICo
/* 1548 */    MCD::OPC_FilterValue, 14, 13, 0, // Skip to: 1565
/* 1552 */    MCD::OPC_CheckField, 16, 5, 0, 4, 0, // Skip to: 1562
/* 1558 */    MCD::OPC_Decode, 134, 5, 17, // Opcode: LI
/* 1562 */    MCD::OPC_Decode, 37, 18, // Opcode: ADDI
/* 1565 */    MCD::OPC_FilterValue, 15, 13, 0, // Skip to: 1582
/* 1569 */    MCD::OPC_CheckField, 16, 5, 0, 4, 0, // Skip to: 1579
/* 1575 */    MCD::OPC_Decode, 136, 5, 17, // Opcode: LIS
/* 1579 */    MCD::OPC_Decode, 42, 18, // Opcode: ADDIS
/* 1582 */    MCD::OPC_FilterValue, 16, 7, 1, // Skip to: 1849
/* 1586 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 1589 */    MCD::OPC_FilterValue, 0, 61, 0, // Skip to: 1654
/* 1593 */    MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 1596 */    MCD::OPC_FilterValue, 128, 4, 4, 0, // Skip to: 1605
/* 1601 */    MCD::OPC_Decode, 150, 1, 19, // Opcode: BDNZ
/* 1605 */    MCD::OPC_FilterValue, 192, 4, 4, 0, // Skip to: 1614
/* 1610 */    MCD::OPC_Decode, 170, 1, 19, // Opcode: BDZ
/* 1614 */    MCD::OPC_FilterValue, 128, 6, 4, 0, // Skip to: 1623
/* 1619 */    MCD::OPC_Decode, 168, 1, 19, // Opcode: BDNZm
/* 1623 */    MCD::OPC_FilterValue, 160, 6, 4, 0, // Skip to: 1632
/* 1628 */    MCD::OPC_Decode, 169, 1, 19, // Opcode: BDNZp
/* 1632 */    MCD::OPC_FilterValue, 192, 6, 4, 0, // Skip to: 1641
/* 1637 */    MCD::OPC_Decode, 188, 1, 19, // Opcode: BDZm
/* 1641 */    MCD::OPC_FilterValue, 224, 6, 4, 0, // Skip to: 1650
/* 1646 */    MCD::OPC_Decode, 189, 1, 19, // Opcode: BDZp
/* 1650 */    MCD::OPC_Decode, 137, 10, 20, // Opcode: gBC
/* 1654 */    MCD::OPC_FilterValue, 1, 61, 0, // Skip to: 1719
/* 1658 */    MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 1661 */    MCD::OPC_FilterValue, 128, 4, 4, 0, // Skip to: 1670
/* 1666 */    MCD::OPC_Decode, 155, 1, 19, // Opcode: BDNZL
/* 1670 */    MCD::OPC_FilterValue, 192, 4, 4, 0, // Skip to: 1679
/* 1675 */    MCD::OPC_Decode, 175, 1, 19, // Opcode: BDZL
/* 1679 */    MCD::OPC_FilterValue, 128, 6, 4, 0, // Skip to: 1688
/* 1684 */    MCD::OPC_Decode, 166, 1, 19, // Opcode: BDNZLm
/* 1688 */    MCD::OPC_FilterValue, 160, 6, 4, 0, // Skip to: 1697
/* 1693 */    MCD::OPC_Decode, 167, 1, 19, // Opcode: BDNZLp
/* 1697 */    MCD::OPC_FilterValue, 192, 6, 4, 0, // Skip to: 1706
/* 1702 */    MCD::OPC_Decode, 186, 1, 19, // Opcode: BDZLm
/* 1706 */    MCD::OPC_FilterValue, 224, 6, 4, 0, // Skip to: 1715
/* 1711 */    MCD::OPC_Decode, 187, 1, 19, // Opcode: BDZLp
/* 1715 */    MCD::OPC_Decode, 141, 10, 20, // Opcode: gBCL
/* 1719 */    MCD::OPC_FilterValue, 2, 61, 0, // Skip to: 1784
/* 1723 */    MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 1726 */    MCD::OPC_FilterValue, 128, 4, 4, 0, // Skip to: 1735
/* 1731 */    MCD::OPC_Decode, 152, 1, 19, // Opcode: BDNZA
/* 1735 */    MCD::OPC_FilterValue, 192, 4, 4, 0, // Skip to: 1744
/* 1740 */    MCD::OPC_Decode, 172, 1, 19, // Opcode: BDZA
/* 1744 */    MCD::OPC_FilterValue, 128, 6, 4, 0, // Skip to: 1753
/* 1749 */    MCD::OPC_Decode, 153, 1, 19, // Opcode: BDNZAm
/* 1753 */    MCD::OPC_FilterValue, 160, 6, 4, 0, // Skip to: 1762
/* 1758 */    MCD::OPC_Decode, 154, 1, 19, // Opcode: BDNZAp
/* 1762 */    MCD::OPC_FilterValue, 192, 6, 4, 0, // Skip to: 1771
/* 1767 */    MCD::OPC_Decode, 173, 1, 19, // Opcode: BDZAm
/* 1771 */    MCD::OPC_FilterValue, 224, 6, 4, 0, // Skip to: 1780
/* 1776 */    MCD::OPC_Decode, 174, 1, 19, // Opcode: BDZAp
/* 1780 */    MCD::OPC_Decode, 138, 10, 20, // Opcode: gBCA
/* 1784 */    MCD::OPC_FilterValue, 3, 59, 30, // Skip to: 9527
/* 1788 */    MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 1791 */    MCD::OPC_FilterValue, 128, 4, 4, 0, // Skip to: 1800
/* 1796 */    MCD::OPC_Decode, 156, 1, 19, // Opcode: BDNZLA
/* 1800 */    MCD::OPC_FilterValue, 192, 4, 4, 0, // Skip to: 1809
/* 1805 */    MCD::OPC_Decode, 176, 1, 19, // Opcode: BDZLA
/* 1809 */    MCD::OPC_FilterValue, 128, 6, 4, 0, // Skip to: 1818
/* 1814 */    MCD::OPC_Decode, 157, 1, 19, // Opcode: BDNZLAm
/* 1818 */    MCD::OPC_FilterValue, 160, 6, 4, 0, // Skip to: 1827
/* 1823 */    MCD::OPC_Decode, 158, 1, 19, // Opcode: BDNZLAp
/* 1827 */    MCD::OPC_FilterValue, 192, 6, 4, 0, // Skip to: 1836
/* 1832 */    MCD::OPC_Decode, 177, 1, 19, // Opcode: BDZLAm
/* 1836 */    MCD::OPC_FilterValue, 224, 6, 4, 0, // Skip to: 1845
/* 1841 */    MCD::OPC_Decode, 178, 1, 19, // Opcode: BDZLAp
/* 1845 */    MCD::OPC_Decode, 142, 10, 20, // Opcode: gBCLA
/* 1849 */    MCD::OPC_FilterValue, 17, 10, 0, // Skip to: 1863
/* 1853 */    MCD::OPC_CheckField, 1, 1, 1, 244, 29, // Skip to: 9527
/* 1859 */    MCD::OPC_Decode, 171, 6, 21, // Opcode: SC
/* 1863 */    MCD::OPC_FilterValue, 18, 33, 0, // Skip to: 1900
/* 1867 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 1870 */    MCD::OPC_FilterValue, 0, 3, 0, // Skip to: 1877
/* 1874 */    MCD::OPC_Decode, 116, 22, // Opcode: B
/* 1877 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 1885
/* 1881 */    MCD::OPC_Decode, 190, 1, 22, // Opcode: BL
/* 1885 */    MCD::OPC_FilterValue, 2, 3, 0, // Skip to: 1892
/* 1889 */    MCD::OPC_Decode, 117, 22, // Opcode: BA
/* 1892 */    MCD::OPC_FilterValue, 3, 207, 29, // Skip to: 9527
/* 1896 */    MCD::OPC_Decode, 196, 1, 22, // Opcode: BLA
/* 1900 */    MCD::OPC_FilterValue, 19, 235, 1, // Skip to: 2395
/* 1904 */    MCD::OPC_ExtractField, 0, 11,  // Inst{10-0} ...
/* 1907 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 1927
/* 1911 */    MCD::OPC_CheckField, 21, 2, 0, 186, 29, // Skip to: 9527
/* 1917 */    MCD::OPC_CheckField, 11, 7, 0, 180, 29, // Skip to: 9527
/* 1923 */    MCD::OPC_Decode, 170, 5, 23, // Opcode: MCRF
/* 1927 */    MCD::OPC_FilterValue, 32, 119, 0, // Skip to: 2050
/* 1931 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 1934 */    MCD::OPC_FilterValue, 0, 165, 29, // Skip to: 9527
/* 1938 */    MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 1941 */    MCD::OPC_FilterValue, 128, 4, 10, 0, // Skip to: 1956
/* 1946 */    MCD::OPC_CheckField, 11, 2, 0, 94, 0, // Skip to: 2046
/* 1952 */    MCD::OPC_Decode, 159, 1, 0, // Opcode: BDNZLR
/* 1956 */    MCD::OPC_FilterValue, 192, 4, 10, 0, // Skip to: 1971
/* 1961 */    MCD::OPC_CheckField, 11, 2, 0, 79, 0, // Skip to: 2046
/* 1967 */    MCD::OPC_Decode, 179, 1, 0, // Opcode: BDZLR
/* 1971 */    MCD::OPC_FilterValue, 128, 5, 10, 0, // Skip to: 1986
/* 1976 */    MCD::OPC_CheckField, 11, 2, 0, 64, 0, // Skip to: 2046
/* 1982 */    MCD::OPC_Decode, 199, 1, 0, // Opcode: BLR
/* 1986 */    MCD::OPC_FilterValue, 128, 6, 10, 0, // Skip to: 2001
/* 1991 */    MCD::OPC_CheckField, 11, 2, 0, 49, 0, // Skip to: 2046
/* 1997 */    MCD::OPC_Decode, 164, 1, 0, // Opcode: BDNZLRm
/* 2001 */    MCD::OPC_FilterValue, 160, 6, 10, 0, // Skip to: 2016
/* 2006 */    MCD::OPC_CheckField, 11, 2, 0, 34, 0, // Skip to: 2046
/* 2012 */    MCD::OPC_Decode, 165, 1, 0, // Opcode: BDNZLRp
/* 2016 */    MCD::OPC_FilterValue, 192, 6, 10, 0, // Skip to: 2031
/* 2021 */    MCD::OPC_CheckField, 11, 2, 0, 19, 0, // Skip to: 2046
/* 2027 */    MCD::OPC_Decode, 184, 1, 0, // Opcode: BDZLRm
/* 2031 */    MCD::OPC_FilterValue, 224, 6, 10, 0, // Skip to: 2046
/* 2036 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 2046
/* 2042 */    MCD::OPC_Decode, 185, 1, 0, // Opcode: BDZLRp
/* 2046 */    MCD::OPC_Decode, 143, 10, 24, // Opcode: gBCLR
/* 2050 */    MCD::OPC_FilterValue, 33, 119, 0, // Skip to: 2173
/* 2054 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 2057 */    MCD::OPC_FilterValue, 0, 42, 29, // Skip to: 9527
/* 2061 */    MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 2064 */    MCD::OPC_FilterValue, 128, 4, 10, 0, // Skip to: 2079
/* 2069 */    MCD::OPC_CheckField, 11, 2, 0, 94, 0, // Skip to: 2169
/* 2075 */    MCD::OPC_Decode, 161, 1, 0, // Opcode: BDNZLRL
/* 2079 */    MCD::OPC_FilterValue, 192, 4, 10, 0, // Skip to: 2094
/* 2084 */    MCD::OPC_CheckField, 11, 2, 0, 79, 0, // Skip to: 2169
/* 2090 */    MCD::OPC_Decode, 181, 1, 0, // Opcode: BDZLRL
/* 2094 */    MCD::OPC_FilterValue, 128, 5, 10, 0, // Skip to: 2109
/* 2099 */    MCD::OPC_CheckField, 11, 2, 0, 64, 0, // Skip to: 2169
/* 2105 */    MCD::OPC_Decode, 201, 1, 0, // Opcode: BLRL
/* 2109 */    MCD::OPC_FilterValue, 128, 6, 10, 0, // Skip to: 2124
/* 2114 */    MCD::OPC_CheckField, 11, 2, 0, 49, 0, // Skip to: 2169
/* 2120 */    MCD::OPC_Decode, 162, 1, 0, // Opcode: BDNZLRLm
/* 2124 */    MCD::OPC_FilterValue, 160, 6, 10, 0, // Skip to: 2139
/* 2129 */    MCD::OPC_CheckField, 11, 2, 0, 34, 0, // Skip to: 2169
/* 2135 */    MCD::OPC_Decode, 163, 1, 0, // Opcode: BDNZLRLp
/* 2139 */    MCD::OPC_FilterValue, 192, 6, 10, 0, // Skip to: 2154
/* 2144 */    MCD::OPC_CheckField, 11, 2, 0, 19, 0, // Skip to: 2169
/* 2150 */    MCD::OPC_Decode, 182, 1, 0, // Opcode: BDZLRLm
/* 2154 */    MCD::OPC_FilterValue, 224, 6, 10, 0, // Skip to: 2169
/* 2159 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 2169
/* 2165 */    MCD::OPC_Decode, 183, 1, 0, // Opcode: BDZLRLp
/* 2169 */    MCD::OPC_Decode, 144, 10, 24, // Opcode: gBCLRL
/* 2173 */    MCD::OPC_FilterValue, 36, 10, 0, // Skip to: 2187
/* 2177 */    MCD::OPC_CheckField, 11, 15, 0, 176, 28, // Skip to: 9527
/* 2183 */    MCD::OPC_Decode, 139, 6, 0, // Opcode: RFID
/* 2187 */    MCD::OPC_FilterValue, 66, 4, 0, // Skip to: 2195
/* 2191 */    MCD::OPC_Decode, 234, 1, 25, // Opcode: CRNOR
/* 2195 */    MCD::OPC_FilterValue, 76, 10, 0, // Skip to: 2209
/* 2199 */    MCD::OPC_CheckField, 11, 15, 0, 154, 28, // Skip to: 9527
/* 2205 */    MCD::OPC_Decode, 140, 6, 0, // Opcode: RFMCI
/* 2209 */    MCD::OPC_FilterValue, 78, 10, 0, // Skip to: 2223
/* 2213 */    MCD::OPC_CheckField, 11, 15, 0, 140, 28, // Skip to: 9527
/* 2219 */    MCD::OPC_Decode, 137, 6, 0, // Opcode: RFDI
/* 2223 */    MCD::OPC_FilterValue, 100, 10, 0, // Skip to: 2237
/* 2227 */    MCD::OPC_CheckField, 11, 15, 0, 126, 28, // Skip to: 9527
/* 2233 */    MCD::OPC_Decode, 138, 6, 0, // Opcode: RFI
/* 2237 */    MCD::OPC_FilterValue, 102, 10, 0, // Skip to: 2251
/* 2241 */    MCD::OPC_CheckField, 11, 15, 0, 112, 28, // Skip to: 9527
/* 2247 */    MCD::OPC_Decode, 136, 6, 0, // Opcode: RFCI
/* 2251 */    MCD::OPC_FilterValue, 130, 2, 4, 0, // Skip to: 2260
/* 2256 */    MCD::OPC_Decode, 231, 1, 25, // Opcode: CRANDC
/* 2260 */    MCD::OPC_FilterValue, 172, 2, 10, 0, // Skip to: 2275
/* 2265 */    MCD::OPC_CheckField, 11, 15, 0, 88, 28, // Skip to: 9527
/* 2271 */    MCD::OPC_Decode, 206, 4, 0, // Opcode: ISYNC
/* 2275 */    MCD::OPC_FilterValue, 130, 3, 4, 0, // Skip to: 2284
/* 2280 */    MCD::OPC_Decode, 239, 1, 25, // Opcode: CRXOR
/* 2284 */    MCD::OPC_FilterValue, 194, 3, 4, 0, // Skip to: 2293
/* 2289 */    MCD::OPC_Decode, 233, 1, 25, // Opcode: CRNAND
/* 2293 */    MCD::OPC_FilterValue, 130, 4, 4, 0, // Skip to: 2302
/* 2298 */    MCD::OPC_Decode, 230, 1, 25, // Opcode: CRAND
/* 2302 */    MCD::OPC_FilterValue, 194, 4, 4, 0, // Skip to: 2311
/* 2307 */    MCD::OPC_Decode, 232, 1, 25, // Opcode: CREQV
/* 2311 */    MCD::OPC_FilterValue, 194, 6, 4, 0, // Skip to: 2320
/* 2316 */    MCD::OPC_Decode, 236, 1, 25, // Opcode: CRORC
/* 2320 */    MCD::OPC_FilterValue, 130, 7, 4, 0, // Skip to: 2329
/* 2325 */    MCD::OPC_Decode, 235, 1, 25, // Opcode: CROR
/* 2329 */    MCD::OPC_FilterValue, 160, 8, 28, 0, // Skip to: 2362
/* 2334 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 2337 */    MCD::OPC_FilterValue, 0, 18, 28, // Skip to: 9527
/* 2341 */    MCD::OPC_CheckField, 16, 10, 128, 5, 10, 0, // Skip to: 2358
/* 2348 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 2358
/* 2354 */    MCD::OPC_Decode, 144, 1, 0, // Opcode: BCTR
/* 2358 */    MCD::OPC_Decode, 139, 10, 24, // Opcode: gBCCTR
/* 2362 */    MCD::OPC_FilterValue, 161, 8, 248, 27, // Skip to: 9527
/* 2367 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 2370 */    MCD::OPC_FilterValue, 0, 241, 27, // Skip to: 9527
/* 2374 */    MCD::OPC_CheckField, 16, 10, 128, 5, 10, 0, // Skip to: 2391
/* 2381 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 2391
/* 2387 */    MCD::OPC_Decode, 146, 1, 0, // Opcode: BCTRL
/* 2391 */    MCD::OPC_Decode, 140, 10, 24, // Opcode: gBCCTRL
/* 2395 */    MCD::OPC_FilterValue, 20, 19, 0, // Skip to: 2418
/* 2399 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2402 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2410
/* 2406 */    MCD::OPC_Decode, 154, 6, 26, // Opcode: RLWIMI
/* 2410 */    MCD::OPC_FilterValue, 1, 201, 27, // Skip to: 9527
/* 2414 */    MCD::OPC_Decode, 157, 6, 26, // Opcode: RLWIMIo
/* 2418 */    MCD::OPC_FilterValue, 21, 19, 0, // Skip to: 2441
/* 2422 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2425 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2433
/* 2429 */    MCD::OPC_Decode, 158, 6, 27, // Opcode: RLWINM
/* 2433 */    MCD::OPC_FilterValue, 1, 178, 27, // Skip to: 9527
/* 2437 */    MCD::OPC_Decode, 161, 6, 27, // Opcode: RLWINMo
/* 2441 */    MCD::OPC_FilterValue, 23, 19, 0, // Skip to: 2464
/* 2445 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2448 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2456
/* 2452 */    MCD::OPC_Decode, 162, 6, 28, // Opcode: RLWNM
/* 2456 */    MCD::OPC_FilterValue, 1, 155, 27, // Skip to: 9527
/* 2460 */    MCD::OPC_Decode, 165, 6, 28, // Opcode: RLWNMo
/* 2464 */    MCD::OPC_FilterValue, 24, 14, 0, // Skip to: 2482
/* 2468 */    MCD::OPC_CheckField, 0, 26, 0, 4, 0, // Skip to: 2478
/* 2474 */    MCD::OPC_Decode, 238, 5, 0, // Opcode: NOP
/* 2478 */    MCD::OPC_Decode, 252, 5, 29, // Opcode: ORI
/* 2482 */    MCD::OPC_FilterValue, 25, 4, 0, // Skip to: 2490
/* 2486 */    MCD::OPC_Decode, 254, 5, 29, // Opcode: ORIS
/* 2490 */    MCD::OPC_FilterValue, 26, 4, 0, // Skip to: 2498
/* 2494 */    MCD::OPC_Decode, 252, 8, 29, // Opcode: XORI
/* 2498 */    MCD::OPC_FilterValue, 27, 4, 0, // Skip to: 2506
/* 2502 */    MCD::OPC_Decode, 254, 8, 29, // Opcode: XORIS
/* 2506 */    MCD::OPC_FilterValue, 28, 3, 0, // Skip to: 2513
/* 2510 */    MCD::OPC_Decode, 76, 29, // Opcode: ANDIo
/* 2513 */    MCD::OPC_FilterValue, 29, 3, 0, // Skip to: 2520
/* 2517 */    MCD::OPC_Decode, 74, 29, // Opcode: ANDISo
/* 2520 */    MCD::OPC_FilterValue, 30, 134, 0, // Skip to: 2658
/* 2524 */    MCD::OPC_ExtractField, 2, 3,  // Inst{4-2} ...
/* 2527 */    MCD::OPC_FilterValue, 0, 19, 0, // Skip to: 2550
/* 2531 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2534 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2542
/* 2538 */    MCD::OPC_Decode, 146, 6, 30, // Opcode: RLDICL
/* 2542 */    MCD::OPC_FilterValue, 1, 69, 27, // Skip to: 9527
/* 2546 */    MCD::OPC_Decode, 148, 6, 30, // Opcode: RLDICLo
/* 2550 */    MCD::OPC_FilterValue, 1, 19, 0, // Skip to: 2573
/* 2554 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2557 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2565
/* 2561 */    MCD::OPC_Decode, 149, 6, 30, // Opcode: RLDICR
/* 2565 */    MCD::OPC_FilterValue, 1, 46, 27, // Skip to: 9527
/* 2569 */    MCD::OPC_Decode, 150, 6, 30, // Opcode: RLDICRo
/* 2573 */    MCD::OPC_FilterValue, 2, 19, 0, // Skip to: 2596
/* 2577 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2580 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2588
/* 2584 */    MCD::OPC_Decode, 145, 6, 30, // Opcode: RLDIC
/* 2588 */    MCD::OPC_FilterValue, 1, 23, 27, // Skip to: 9527
/* 2592 */    MCD::OPC_Decode, 151, 6, 30, // Opcode: RLDICo
/* 2596 */    MCD::OPC_FilterValue, 3, 19, 0, // Skip to: 2619
/* 2600 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 2603 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2611
/* 2607 */    MCD::OPC_Decode, 152, 6, 31, // Opcode: RLDIMI
/* 2611 */    MCD::OPC_FilterValue, 1, 0, 27, // Skip to: 9527
/* 2615 */    MCD::OPC_Decode, 153, 6, 31, // Opcode: RLDIMIo
/* 2619 */    MCD::OPC_FilterValue, 4, 248, 26, // Skip to: 9527
/* 2623 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 2626 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2634
/* 2630 */    MCD::OPC_Decode, 141, 6, 32, // Opcode: RLDCL
/* 2634 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 2642
/* 2638 */    MCD::OPC_Decode, 142, 6, 32, // Opcode: RLDCLo
/* 2642 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 2650
/* 2646 */    MCD::OPC_Decode, 143, 6, 32, // Opcode: RLDCR
/* 2650 */    MCD::OPC_FilterValue, 3, 217, 26, // Skip to: 9527
/* 2654 */    MCD::OPC_Decode, 144, 6, 32, // Opcode: RLDCRo
/* 2658 */    MCD::OPC_FilterValue, 31, 179, 12, // Skip to: 5913
/* 2662 */    MCD::OPC_ExtractField, 2, 4,  // Inst{5-2} ...
/* 2665 */    MCD::OPC_FilterValue, 0, 73, 0, // Skip to: 2742
/* 2669 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 2672 */    MCD::OPC_FilterValue, 0, 31, 0, // Skip to: 2707
/* 2676 */    MCD::OPC_ExtractField, 21, 2,  // Inst{22-21} ...
/* 2679 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 2693
/* 2683 */    MCD::OPC_CheckField, 0, 2, 0, 182, 26, // Skip to: 9527
/* 2689 */    MCD::OPC_Decode, 220, 1, 33, // Opcode: CMPW
/* 2693 */    MCD::OPC_FilterValue, 1, 174, 26, // Skip to: 9527
/* 2697 */    MCD::OPC_CheckField, 0, 2, 0, 168, 26, // Skip to: 9527
/* 2703 */    MCD::OPC_Decode, 214, 1, 34, // Opcode: CMPD
/* 2707 */    MCD::OPC_FilterValue, 1, 160, 26, // Skip to: 9527
/* 2711 */    MCD::OPC_ExtractField, 21, 2,  // Inst{22-21} ...
/* 2714 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 2728
/* 2718 */    MCD::OPC_CheckField, 0, 2, 0, 147, 26, // Skip to: 9527
/* 2724 */    MCD::OPC_Decode, 218, 1, 33, // Opcode: CMPLW
/* 2728 */    MCD::OPC_FilterValue, 1, 139, 26, // Skip to: 9527
/* 2732 */    MCD::OPC_CheckField, 0, 2, 0, 133, 26, // Skip to: 9527
/* 2738 */    MCD::OPC_Decode, 216, 1, 34, // Opcode: CMPLD
/* 2742 */    MCD::OPC_FilterValue, 1, 65, 0, // Skip to: 2811
/* 2746 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 2749 */    MCD::OPC_FilterValue, 4, 16, 0, // Skip to: 2769
/* 2753 */    MCD::OPC_CheckField, 16, 1, 0, 112, 26, // Skip to: 9527
/* 2759 */    MCD::OPC_CheckField, 1, 1, 1, 106, 26, // Skip to: 9527
/* 2765 */    MCD::OPC_Decode, 247, 8, 35, // Opcode: WRTEE
/* 2769 */    MCD::OPC_FilterValue, 5, 10, 0, // Skip to: 2783
/* 2773 */    MCD::OPC_CheckField, 1, 1, 1, 92, 26, // Skip to: 9527
/* 2779 */    MCD::OPC_Decode, 248, 8, 36, // Opcode: WRTEEI
/* 2783 */    MCD::OPC_FilterValue, 10, 10, 0, // Skip to: 2797
/* 2787 */    MCD::OPC_CheckField, 0, 2, 2, 78, 26, // Skip to: 9527
/* 2793 */    MCD::OPC_Decode, 175, 5, 37, // Opcode: MFDCR
/* 2797 */    MCD::OPC_FilterValue, 14, 70, 26, // Skip to: 9527
/* 2801 */    MCD::OPC_CheckField, 0, 2, 2, 64, 26, // Skip to: 9527
/* 2807 */    MCD::OPC_Decode, 197, 5, 37, // Opcode: MTDCR
/* 2811 */    MCD::OPC_FilterValue, 2, 44, 0, // Skip to: 2859
/* 2815 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 2818 */    MCD::OPC_FilterValue, 0, 23, 0, // Skip to: 2845
/* 2822 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 2825 */    MCD::OPC_FilterValue, 0, 42, 26, // Skip to: 9527
/* 2829 */    MCD::OPC_CheckField, 11, 15, 128, 248, 1, 4, 0, // Skip to: 2841
/* 2837 */    MCD::OPC_Decode, 204, 7, 0, // Opcode: TRAP
/* 2841 */    MCD::OPC_Decode, 205, 7, 38, // Opcode: TW
/* 2845 */    MCD::OPC_FilterValue, 2, 22, 26, // Skip to: 9527
/* 2849 */    MCD::OPC_CheckField, 0, 2, 0, 16, 26, // Skip to: 9527
/* 2855 */    MCD::OPC_Decode, 188, 7, 39, // Opcode: TD
/* 2859 */    MCD::OPC_FilterValue, 3, 201, 0, // Skip to: 3064
/* 2863 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 2866 */    MCD::OPC_FilterValue, 0, 19, 0, // Skip to: 2889
/* 2870 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 2873 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2881
/* 2877 */    MCD::OPC_Decode, 143, 5, 40, // Opcode: LVSL
/* 2881 */    MCD::OPC_FilterValue, 2, 242, 25, // Skip to: 9527
/* 2885 */    MCD::OPC_Decode, 140, 5, 40, // Opcode: LVEBX
/* 2889 */    MCD::OPC_FilterValue, 1, 19, 0, // Skip to: 2912
/* 2893 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 2896 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 2904
/* 2900 */    MCD::OPC_Decode, 144, 5, 40, // Opcode: LVSR
/* 2904 */    MCD::OPC_FilterValue, 2, 219, 25, // Skip to: 9527
/* 2908 */    MCD::OPC_Decode, 141, 5, 40, // Opcode: LVEHX
/* 2912 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 2926
/* 2916 */    MCD::OPC_CheckField, 0, 2, 2, 205, 25, // Skip to: 9527
/* 2922 */    MCD::OPC_Decode, 142, 5, 40, // Opcode: LVEWX
/* 2926 */    MCD::OPC_FilterValue, 3, 10, 0, // Skip to: 2940
/* 2930 */    MCD::OPC_CheckField, 0, 2, 2, 191, 25, // Skip to: 9527
/* 2936 */    MCD::OPC_Decode, 145, 5, 40, // Opcode: LVX
/* 2940 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 2954
/* 2944 */    MCD::OPC_CheckField, 0, 2, 2, 177, 25, // Skip to: 9527
/* 2950 */    MCD::OPC_Decode, 130, 7, 40, // Opcode: STVEBX
/* 2954 */    MCD::OPC_FilterValue, 5, 10, 0, // Skip to: 2968
/* 2958 */    MCD::OPC_CheckField, 0, 2, 2, 163, 25, // Skip to: 9527
/* 2964 */    MCD::OPC_Decode, 131, 7, 40, // Opcode: STVEHX
/* 2968 */    MCD::OPC_FilterValue, 6, 10, 0, // Skip to: 2982
/* 2972 */    MCD::OPC_CheckField, 0, 2, 2, 149, 25, // Skip to: 9527
/* 2978 */    MCD::OPC_Decode, 132, 7, 40, // Opcode: STVEWX
/* 2982 */    MCD::OPC_FilterValue, 7, 10, 0, // Skip to: 2996
/* 2986 */    MCD::OPC_CheckField, 0, 2, 2, 135, 25, // Skip to: 9527
/* 2992 */    MCD::OPC_Decode, 133, 7, 40, // Opcode: STVX
/* 2996 */    MCD::OPC_FilterValue, 11, 10, 0, // Skip to: 3010
/* 3000 */    MCD::OPC_CheckField, 0, 2, 2, 121, 25, // Skip to: 9527
/* 3006 */    MCD::OPC_Decode, 146, 5, 40, // Opcode: LVXL
/* 3010 */    MCD::OPC_FilterValue, 14, 16, 0, // Skip to: 3030
/* 3014 */    MCD::OPC_CheckField, 21, 5, 0, 107, 25, // Skip to: 9527
/* 3020 */    MCD::OPC_CheckField, 0, 2, 0, 101, 25, // Skip to: 9527
/* 3026 */    MCD::OPC_Decode, 248, 1, 41, // Opcode: DCCCI
/* 3030 */    MCD::OPC_FilterValue, 15, 10, 0, // Skip to: 3044
/* 3034 */    MCD::OPC_CheckField, 0, 2, 2, 87, 25, // Skip to: 9527
/* 3040 */    MCD::OPC_Decode, 134, 7, 40, // Opcode: STVXL
/* 3044 */    MCD::OPC_FilterValue, 30, 79, 25, // Skip to: 9527
/* 3048 */    MCD::OPC_CheckField, 21, 5, 0, 73, 25, // Skip to: 9527
/* 3054 */    MCD::OPC_CheckField, 0, 2, 0, 67, 25, // Skip to: 9527
/* 3060 */    MCD::OPC_Decode, 197, 4, 41, // Opcode: ICCCI
/* 3064 */    MCD::OPC_FilterValue, 4, 22, 1, // Skip to: 3346
/* 3068 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3071 */    MCD::OPC_FilterValue, 0, 35, 0, // Skip to: 3110
/* 3075 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3078 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 3086
/* 3082 */    MCD::OPC_Decode, 152, 7, 42, // Opcode: SUBFC
/* 3086 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 3094
/* 3090 */    MCD::OPC_Decode, 155, 7, 42, // Opcode: SUBFCo
/* 3094 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3102
/* 3098 */    MCD::OPC_Decode, 214, 5, 43, // Opcode: MULHDU
/* 3102 */    MCD::OPC_FilterValue, 3, 21, 25, // Skip to: 9527
/* 3106 */    MCD::OPC_Decode, 215, 5, 43, // Opcode: MULHDUo
/* 3110 */    MCD::OPC_FilterValue, 1, 19, 0, // Skip to: 3133
/* 3114 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3117 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 3125
/* 3121 */    MCD::OPC_Decode, 149, 7, 42, // Opcode: SUBF
/* 3125 */    MCD::OPC_FilterValue, 1, 254, 24, // Skip to: 9527
/* 3129 */    MCD::OPC_Decode, 170, 7, 42, // Opcode: SUBFo
/* 3133 */    MCD::OPC_FilterValue, 2, 19, 0, // Skip to: 3156
/* 3137 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3140 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3148
/* 3144 */    MCD::OPC_Decode, 213, 5, 43, // Opcode: MULHD
/* 3148 */    MCD::OPC_FilterValue, 3, 231, 24, // Skip to: 9527
/* 3152 */    MCD::OPC_Decode, 216, 5, 43, // Opcode: MULHDo
/* 3156 */    MCD::OPC_FilterValue, 3, 31, 0, // Skip to: 3191
/* 3160 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3163 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 3177
/* 3167 */    MCD::OPC_CheckField, 11, 5, 0, 210, 24, // Skip to: 9527
/* 3173 */    MCD::OPC_Decode, 234, 5, 44, // Opcode: NEG
/* 3177 */    MCD::OPC_FilterValue, 1, 202, 24, // Skip to: 9527
/* 3181 */    MCD::OPC_CheckField, 11, 5, 0, 196, 24, // Skip to: 9527
/* 3187 */    MCD::OPC_Decode, 237, 5, 44, // Opcode: NEGo
/* 3191 */    MCD::OPC_FilterValue, 4, 19, 0, // Skip to: 3214
/* 3195 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3198 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 3206
/* 3202 */    MCD::OPC_Decode, 156, 7, 42, // Opcode: SUBFE
/* 3206 */    MCD::OPC_FilterValue, 1, 173, 24, // Skip to: 9527
/* 3210 */    MCD::OPC_Decode, 159, 7, 42, // Opcode: SUBFEo
/* 3214 */    MCD::OPC_FilterValue, 6, 31, 0, // Skip to: 3249
/* 3218 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3221 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 3235
/* 3225 */    MCD::OPC_CheckField, 11, 5, 0, 152, 24, // Skip to: 9527
/* 3231 */    MCD::OPC_Decode, 166, 7, 44, // Opcode: SUBFZE
/* 3235 */    MCD::OPC_FilterValue, 1, 144, 24, // Skip to: 9527
/* 3239 */    MCD::OPC_CheckField, 11, 5, 0, 138, 24, // Skip to: 9527
/* 3245 */    MCD::OPC_Decode, 169, 7, 44, // Opcode: SUBFZEo
/* 3249 */    MCD::OPC_FilterValue, 7, 47, 0, // Skip to: 3300
/* 3253 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3256 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 3270
/* 3260 */    MCD::OPC_CheckField, 11, 5, 0, 117, 24, // Skip to: 9527
/* 3266 */    MCD::OPC_Decode, 162, 7, 44, // Opcode: SUBFME
/* 3270 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 3284
/* 3274 */    MCD::OPC_CheckField, 11, 5, 0, 103, 24, // Skip to: 9527
/* 3280 */    MCD::OPC_Decode, 165, 7, 44, // Opcode: SUBFMEo
/* 3284 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3292
/* 3288 */    MCD::OPC_Decode, 221, 5, 43, // Opcode: MULLD
/* 3292 */    MCD::OPC_FilterValue, 3, 87, 24, // Skip to: 9527
/* 3296 */    MCD::OPC_Decode, 222, 5, 43, // Opcode: MULLDo
/* 3300 */    MCD::OPC_FilterValue, 14, 19, 0, // Skip to: 3323
/* 3304 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3307 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3315
/* 3311 */    MCD::OPC_Decode, 250, 1, 43, // Opcode: DIVDU
/* 3315 */    MCD::OPC_FilterValue, 3, 64, 24, // Skip to: 9527
/* 3319 */    MCD::OPC_Decode, 251, 1, 43, // Opcode: DIVDUo
/* 3323 */    MCD::OPC_FilterValue, 15, 56, 24, // Skip to: 9527
/* 3327 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3330 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3338
/* 3334 */    MCD::OPC_Decode, 249, 1, 43, // Opcode: DIVD
/* 3338 */    MCD::OPC_FilterValue, 3, 41, 24, // Skip to: 9527
/* 3342 */    MCD::OPC_Decode, 252, 1, 43, // Opcode: DIVDo
/* 3346 */    MCD::OPC_FilterValue, 5, 233, 0, // Skip to: 3583
/* 3350 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3353 */    MCD::OPC_FilterValue, 0, 33, 0, // Skip to: 3390
/* 3357 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3360 */    MCD::OPC_FilterValue, 0, 3, 0, // Skip to: 3367
/* 3364 */    MCD::OPC_Decode, 29, 42, // Opcode: ADDC
/* 3367 */    MCD::OPC_FilterValue, 1, 3, 0, // Skip to: 3374
/* 3371 */    MCD::OPC_Decode, 32, 42, // Opcode: ADDCo
/* 3374 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3382
/* 3378 */    MCD::OPC_Decode, 218, 5, 42, // Opcode: MULHWU
/* 3382 */    MCD::OPC_FilterValue, 3, 253, 23, // Skip to: 9527
/* 3386 */    MCD::OPC_Decode, 219, 5, 42, // Opcode: MULHWUo
/* 3390 */    MCD::OPC_FilterValue, 2, 19, 0, // Skip to: 3413
/* 3394 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3397 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3405
/* 3401 */    MCD::OPC_Decode, 217, 5, 42, // Opcode: MULHW
/* 3405 */    MCD::OPC_FilterValue, 3, 230, 23, // Skip to: 9527
/* 3409 */    MCD::OPC_Decode, 220, 5, 42, // Opcode: MULHWo
/* 3413 */    MCD::OPC_FilterValue, 4, 17, 0, // Skip to: 3434
/* 3417 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3420 */    MCD::OPC_FilterValue, 0, 3, 0, // Skip to: 3427
/* 3424 */    MCD::OPC_Decode, 33, 42, // Opcode: ADDE
/* 3427 */    MCD::OPC_FilterValue, 1, 208, 23, // Skip to: 9527
/* 3431 */    MCD::OPC_Decode, 36, 42, // Opcode: ADDEo
/* 3434 */    MCD::OPC_FilterValue, 6, 29, 0, // Skip to: 3467
/* 3438 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3441 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 3454
/* 3445 */    MCD::OPC_CheckField, 11, 5, 0, 188, 23, // Skip to: 9527
/* 3451 */    MCD::OPC_Decode, 61, 44, // Opcode: ADDZE
/* 3454 */    MCD::OPC_FilterValue, 1, 181, 23, // Skip to: 9527
/* 3458 */    MCD::OPC_CheckField, 11, 5, 0, 175, 23, // Skip to: 9527
/* 3464 */    MCD::OPC_Decode, 64, 44, // Opcode: ADDZEo
/* 3467 */    MCD::OPC_FilterValue, 7, 45, 0, // Skip to: 3516
/* 3471 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3474 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 3487
/* 3478 */    MCD::OPC_CheckField, 11, 5, 0, 155, 23, // Skip to: 9527
/* 3484 */    MCD::OPC_Decode, 57, 44, // Opcode: ADDME
/* 3487 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 3500
/* 3491 */    MCD::OPC_CheckField, 11, 5, 0, 142, 23, // Skip to: 9527
/* 3497 */    MCD::OPC_Decode, 60, 44, // Opcode: ADDMEo
/* 3500 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3508
/* 3504 */    MCD::OPC_Decode, 225, 5, 42, // Opcode: MULLW
/* 3508 */    MCD::OPC_FilterValue, 3, 127, 23, // Skip to: 9527
/* 3512 */    MCD::OPC_Decode, 226, 5, 42, // Opcode: MULLWo
/* 3516 */    MCD::OPC_FilterValue, 8, 17, 0, // Skip to: 3537
/* 3520 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3523 */    MCD::OPC_FilterValue, 0, 3, 0, // Skip to: 3530
/* 3527 */    MCD::OPC_Decode, 22, 42, // Opcode: ADD4
/* 3530 */    MCD::OPC_FilterValue, 1, 105, 23, // Skip to: 9527
/* 3534 */    MCD::OPC_Decode, 24, 42, // Opcode: ADD4o
/* 3537 */    MCD::OPC_FilterValue, 14, 19, 0, // Skip to: 3560
/* 3541 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3544 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3552
/* 3548 */    MCD::OPC_Decode, 254, 1, 42, // Opcode: DIVWU
/* 3552 */    MCD::OPC_FilterValue, 3, 83, 23, // Skip to: 9527
/* 3556 */    MCD::OPC_Decode, 255, 1, 42, // Opcode: DIVWUo
/* 3560 */    MCD::OPC_FilterValue, 15, 75, 23, // Skip to: 9527
/* 3564 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3567 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 3575
/* 3571 */    MCD::OPC_Decode, 253, 1, 42, // Opcode: DIVW
/* 3575 */    MCD::OPC_FilterValue, 3, 60, 23, // Skip to: 9527
/* 3579 */    MCD::OPC_Decode, 128, 2, 42, // Opcode: DIVWo
/* 3583 */    MCD::OPC_FilterValue, 6, 101, 0, // Skip to: 3688
/* 3587 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3590 */    MCD::OPC_FilterValue, 10, 10, 0, // Skip to: 3604
/* 3594 */    MCD::OPC_CheckField, 1, 1, 0, 39, 23, // Skip to: 9527
/* 3600 */    MCD::OPC_Decode, 167, 5, 45, // Opcode: LXVDSX
/* 3604 */    MCD::OPC_FilterValue, 18, 10, 0, // Skip to: 3618
/* 3608 */    MCD::OPC_CheckField, 1, 1, 0, 25, 23, // Skip to: 9527
/* 3614 */    MCD::OPC_Decode, 165, 5, 46, // Opcode: LXSDX
/* 3618 */    MCD::OPC_FilterValue, 22, 10, 0, // Skip to: 3632
/* 3622 */    MCD::OPC_CheckField, 1, 1, 0, 11, 23, // Skip to: 9527
/* 3628 */    MCD::OPC_Decode, 146, 7, 46, // Opcode: STXSDX
/* 3632 */    MCD::OPC_FilterValue, 24, 10, 0, // Skip to: 3646
/* 3636 */    MCD::OPC_CheckField, 1, 1, 0, 253, 22, // Skip to: 9527
/* 3642 */    MCD::OPC_Decode, 168, 5, 45, // Opcode: LXVW4X
/* 3646 */    MCD::OPC_FilterValue, 26, 10, 0, // Skip to: 3660
/* 3650 */    MCD::OPC_CheckField, 1, 1, 0, 239, 22, // Skip to: 9527
/* 3656 */    MCD::OPC_Decode, 166, 5, 45, // Opcode: LXVD2X
/* 3660 */    MCD::OPC_FilterValue, 28, 10, 0, // Skip to: 3674
/* 3664 */    MCD::OPC_CheckField, 1, 1, 0, 225, 22, // Skip to: 9527
/* 3670 */    MCD::OPC_Decode, 148, 7, 45, // Opcode: STXVW4X
/* 3674 */    MCD::OPC_FilterValue, 30, 217, 22, // Skip to: 9527
/* 3678 */    MCD::OPC_CheckField, 1, 1, 0, 211, 22, // Skip to: 9527
/* 3684 */    MCD::OPC_Decode, 147, 7, 45, // Opcode: STXVD2X
/* 3688 */    MCD::OPC_FilterValue, 7, 10, 0, // Skip to: 3702
/* 3692 */    MCD::OPC_CheckField, 0, 2, 2, 197, 22, // Skip to: 9527
/* 3698 */    MCD::OPC_Decode, 204, 4, 47, // Opcode: ISEL
/* 3702 */    MCD::OPC_FilterValue, 8, 43, 0, // Skip to: 3749
/* 3706 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 3709 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 3729
/* 3713 */    MCD::OPC_CheckField, 6, 6, 4, 176, 22, // Skip to: 9527
/* 3719 */    MCD::OPC_CheckField, 0, 2, 0, 170, 22, // Skip to: 9527
/* 3725 */    MCD::OPC_Decode, 191, 5, 48, // Opcode: MTCRF
/* 3729 */    MCD::OPC_FilterValue, 1, 162, 22, // Skip to: 9527
/* 3733 */    MCD::OPC_CheckField, 6, 6, 4, 156, 22, // Skip to: 9527
/* 3739 */    MCD::OPC_CheckField, 0, 2, 0, 150, 22, // Skip to: 9527
/* 3745 */    MCD::OPC_Decode, 205, 5, 49, // Opcode: MTOCRF
/* 3749 */    MCD::OPC_FilterValue, 9, 246, 1, // Skip to: 4255
/* 3753 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3756 */    MCD::OPC_FilterValue, 0, 43, 0, // Skip to: 3803
/* 3760 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 3763 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 3783
/* 3767 */    MCD::OPC_CheckField, 11, 9, 0, 122, 22, // Skip to: 9527
/* 3773 */    MCD::OPC_CheckField, 0, 2, 2, 116, 22, // Skip to: 9527
/* 3779 */    MCD::OPC_Decode, 171, 5, 35, // Opcode: MFCR
/* 3783 */    MCD::OPC_FilterValue, 1, 108, 22, // Skip to: 9527
/* 3787 */    MCD::OPC_CheckField, 11, 1, 0, 102, 22, // Skip to: 9527
/* 3793 */    MCD::OPC_CheckField, 0, 2, 2, 96, 22, // Skip to: 9527
/* 3799 */    MCD::OPC_Decode, 180, 5, 50, // Opcode: MFOCRF
/* 3803 */    MCD::OPC_FilterValue, 2, 16, 0, // Skip to: 3823
/* 3807 */    MCD::OPC_CheckField, 11, 10, 0, 82, 22, // Skip to: 9527
/* 3813 */    MCD::OPC_CheckField, 0, 2, 2, 76, 22, // Skip to: 9527
/* 3819 */    MCD::OPC_Decode, 179, 5, 35, // Opcode: MFMSR
/* 3823 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 3837
/* 3827 */    MCD::OPC_CheckField, 1, 1, 0, 62, 22, // Skip to: 9527
/* 3833 */    MCD::OPC_Decode, 203, 5, 51, // Opcode: MTMSR
/* 3837 */    MCD::OPC_FilterValue, 5, 10, 0, // Skip to: 3851
/* 3841 */    MCD::OPC_CheckField, 1, 1, 0, 48, 22, // Skip to: 9527
/* 3847 */    MCD::OPC_Decode, 204, 5, 51, // Opcode: MTMSRD
/* 3851 */    MCD::OPC_FilterValue, 6, 10, 0, // Skip to: 3865
/* 3855 */    MCD::OPC_CheckField, 1, 1, 0, 34, 22, // Skip to: 9527
/* 3861 */    MCD::OPC_Decode, 208, 5, 52, // Opcode: MTSR
/* 3865 */    MCD::OPC_FilterValue, 7, 10, 0, // Skip to: 3879
/* 3869 */    MCD::OPC_CheckField, 1, 1, 0, 20, 22, // Skip to: 9527
/* 3875 */    MCD::OPC_Decode, 209, 5, 53, // Opcode: MTSRIN
/* 3879 */    MCD::OPC_FilterValue, 8, 16, 0, // Skip to: 3899
/* 3883 */    MCD::OPC_CheckField, 16, 10, 0, 6, 22, // Skip to: 9527
/* 3889 */    MCD::OPC_CheckField, 0, 2, 0, 0, 22, // Skip to: 9527
/* 3895 */    MCD::OPC_Decode, 192, 7, 54, // Opcode: TLBIEL
/* 3899 */    MCD::OPC_FilterValue, 9, 16, 0, // Skip to: 3919
/* 3903 */    MCD::OPC_CheckField, 16, 5, 0, 242, 21, // Skip to: 9527
/* 3909 */    MCD::OPC_CheckField, 0, 2, 0, 236, 21, // Skip to: 9527
/* 3915 */    MCD::OPC_Decode, 191, 7, 53, // Opcode: TLBIE
/* 3919 */    MCD::OPC_FilterValue, 10, 32, 0, // Skip to: 3955
/* 3923 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3926 */    MCD::OPC_FilterValue, 2, 221, 21, // Skip to: 9527
/* 3930 */    MCD::OPC_ExtractField, 11, 10,  // Inst{20-11} ...
/* 3933 */    MCD::OPC_FilterValue, 128, 2, 4, 0, // Skip to: 3942
/* 3938 */    MCD::OPC_Decode, 177, 5, 35, // Opcode: MFLR
/* 3942 */    MCD::OPC_FilterValue, 160, 2, 4, 0, // Skip to: 3951
/* 3947 */    MCD::OPC_Decode, 173, 5, 35, // Opcode: MFCTR
/* 3951 */    MCD::OPC_Decode, 182, 5, 37, // Opcode: MFSPR
/* 3955 */    MCD::OPC_FilterValue, 11, 25, 0, // Skip to: 3984
/* 3959 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 3962 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 3976
/* 3966 */    MCD::OPC_CheckField, 11, 15, 0, 179, 21, // Skip to: 9527
/* 3972 */    MCD::OPC_Decode, 190, 7, 0, // Opcode: TLBIA
/* 3976 */    MCD::OPC_FilterValue, 2, 171, 21, // Skip to: 9527
/* 3980 */    MCD::OPC_Decode, 185, 5, 37, // Opcode: MFTB
/* 3984 */    MCD::OPC_FilterValue, 12, 16, 0, // Skip to: 4004
/* 3988 */    MCD::OPC_CheckField, 16, 5, 0, 157, 21, // Skip to: 9527
/* 3994 */    MCD::OPC_CheckField, 0, 2, 0, 151, 21, // Skip to: 9527
/* 4000 */    MCD::OPC_Decode, 189, 6, 53, // Opcode: SLBMTE
/* 4004 */    MCD::OPC_FilterValue, 13, 16, 0, // Skip to: 4024
/* 4008 */    MCD::OPC_CheckField, 16, 10, 0, 137, 21, // Skip to: 9527
/* 4014 */    MCD::OPC_CheckField, 0, 2, 0, 131, 21, // Skip to: 9527
/* 4020 */    MCD::OPC_Decode, 187, 6, 54, // Opcode: SLBIE
/* 4024 */    MCD::OPC_FilterValue, 14, 32, 0, // Skip to: 4060
/* 4028 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4031 */    MCD::OPC_FilterValue, 2, 116, 21, // Skip to: 9527
/* 4035 */    MCD::OPC_ExtractField, 11, 10,  // Inst{20-11} ...
/* 4038 */    MCD::OPC_FilterValue, 128, 2, 4, 0, // Skip to: 4047
/* 4043 */    MCD::OPC_Decode, 201, 5, 35, // Opcode: MTLR
/* 4047 */    MCD::OPC_FilterValue, 160, 2, 4, 0, // Skip to: 4056
/* 4052 */    MCD::OPC_Decode, 193, 5, 35, // Opcode: MTCTR
/* 4056 */    MCD::OPC_Decode, 207, 5, 55, // Opcode: MTSPR
/* 4060 */    MCD::OPC_FilterValue, 15, 16, 0, // Skip to: 4080
/* 4064 */    MCD::OPC_CheckField, 11, 15, 0, 81, 21, // Skip to: 9527
/* 4070 */    MCD::OPC_CheckField, 0, 2, 0, 75, 21, // Skip to: 9527
/* 4076 */    MCD::OPC_Decode, 186, 6, 0, // Opcode: SLBIA
/* 4080 */    MCD::OPC_FilterValue, 18, 10, 0, // Skip to: 4094
/* 4084 */    MCD::OPC_CheckField, 1, 1, 1, 61, 21, // Skip to: 9527
/* 4090 */    MCD::OPC_Decode, 183, 5, 52, // Opcode: MFSR
/* 4094 */    MCD::OPC_FilterValue, 20, 10, 0, // Skip to: 4108
/* 4098 */    MCD::OPC_CheckField, 1, 1, 1, 47, 21, // Skip to: 9527
/* 4104 */    MCD::OPC_Decode, 184, 5, 53, // Opcode: MFSRIN
/* 4108 */    MCD::OPC_FilterValue, 24, 16, 0, // Skip to: 4128
/* 4112 */    MCD::OPC_CheckField, 21, 5, 0, 33, 21, // Skip to: 9527
/* 4118 */    MCD::OPC_CheckField, 0, 2, 0, 27, 21, // Skip to: 9527
/* 4124 */    MCD::OPC_Decode, 193, 7, 41, // Opcode: TLBIVAX
/* 4128 */    MCD::OPC_FilterValue, 28, 43, 0, // Skip to: 4175
/* 4132 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4135 */    MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 4153
/* 4139 */    MCD::OPC_CheckField, 21, 5, 0, 4, 0, // Skip to: 4149
/* 4145 */    MCD::OPC_Decode, 198, 7, 41, // Opcode: TLBSX
/* 4149 */    MCD::OPC_Decode, 199, 7, 42, // Opcode: TLBSX2
/* 4153 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 4161
/* 4157 */    MCD::OPC_Decode, 200, 7, 42, // Opcode: TLBSX2D
/* 4161 */    MCD::OPC_FilterValue, 2, 242, 20, // Skip to: 9527
/* 4165 */    MCD::OPC_CheckField, 16, 5, 0, 236, 20, // Skip to: 9527
/* 4171 */    MCD::OPC_Decode, 188, 6, 53, // Opcode: SLBMFEE
/* 4175 */    MCD::OPC_FilterValue, 29, 21, 0, // Skip to: 4200
/* 4179 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4182 */    MCD::OPC_FilterValue, 0, 221, 20, // Skip to: 9527
/* 4186 */    MCD::OPC_CheckField, 11, 15, 0, 4, 0, // Skip to: 4196
/* 4192 */    MCD::OPC_Decode, 196, 7, 0, // Opcode: TLBRE
/* 4196 */    MCD::OPC_Decode, 197, 7, 56, // Opcode: TLBRE2
/* 4200 */    MCD::OPC_FilterValue, 30, 31, 0, // Skip to: 4235
/* 4204 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4207 */    MCD::OPC_FilterValue, 0, 196, 20, // Skip to: 9527
/* 4211 */    MCD::OPC_CheckField, 11, 15, 0, 4, 0, // Skip to: 4221
/* 4217 */    MCD::OPC_Decode, 202, 7, 0, // Opcode: TLBWE
/* 4221 */    MCD::OPC_CheckField, 16, 10, 0, 4, 0, // Skip to: 4231
/* 4227 */    MCD::OPC_Decode, 194, 7, 54, // Opcode: TLBLD
/* 4231 */    MCD::OPC_Decode, 203, 7, 56, // Opcode: TLBWE2
/* 4235 */    MCD::OPC_FilterValue, 31, 168, 20, // Skip to: 9527
/* 4239 */    MCD::OPC_CheckField, 16, 10, 0, 162, 20, // Skip to: 9527
/* 4245 */    MCD::OPC_CheckField, 0, 2, 0, 156, 20, // Skip to: 9527
/* 4251 */    MCD::OPC_Decode, 195, 7, 54, // Opcode: TLBLI
/* 4255 */    MCD::OPC_FilterValue, 10, 22, 1, // Skip to: 4537
/* 4259 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 4262 */    MCD::OPC_FilterValue, 0, 19, 0, // Skip to: 4285
/* 4266 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4269 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 4277
/* 4273 */    MCD::OPC_Decode, 148, 5, 57, // Opcode: LWARX
/* 4277 */    MCD::OPC_FilterValue, 2, 126, 20, // Skip to: 9527
/* 4281 */    MCD::OPC_Decode, 224, 4, 58, // Opcode: LDX
/* 4285 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 4299
/* 4289 */    MCD::OPC_CheckField, 0, 2, 2, 112, 20, // Skip to: 9527
/* 4295 */    MCD::OPC_Decode, 223, 4, 59, // Opcode: LDUX
/* 4299 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 4313
/* 4303 */    MCD::OPC_CheckField, 0, 2, 0, 98, 20, // Skip to: 9527
/* 4309 */    MCD::OPC_Decode, 219, 4, 58, // Opcode: LDARX
/* 4313 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 4327
/* 4317 */    MCD::OPC_CheckField, 0, 2, 2, 84, 20, // Skip to: 9527
/* 4323 */    MCD::OPC_Decode, 236, 6, 58, // Opcode: STDX
/* 4327 */    MCD::OPC_FilterValue, 5, 10, 0, // Skip to: 4341
/* 4331 */    MCD::OPC_CheckField, 0, 2, 2, 70, 20, // Skip to: 9527
/* 4337 */    MCD::OPC_Decode, 235, 6, 60, // Opcode: STDUX
/* 4341 */    MCD::OPC_FilterValue, 10, 10, 0, // Skip to: 4355
/* 4345 */    MCD::OPC_CheckField, 0, 2, 2, 56, 20, // Skip to: 9527
/* 4351 */    MCD::OPC_Decode, 150, 5, 58, // Opcode: LWAX
/* 4355 */    MCD::OPC_FilterValue, 11, 10, 0, // Skip to: 4369
/* 4359 */    MCD::OPC_CheckField, 0, 2, 2, 42, 20, // Skip to: 9527
/* 4365 */    MCD::OPC_Decode, 149, 5, 59, // Opcode: LWAUX
/* 4369 */    MCD::OPC_FilterValue, 16, 10, 0, // Skip to: 4383
/* 4373 */    MCD::OPC_CheckField, 0, 2, 0, 28, 20, // Skip to: 9527
/* 4379 */    MCD::OPC_Decode, 220, 4, 58, // Opcode: LDBRX
/* 4383 */    MCD::OPC_FilterValue, 18, 10, 0, // Skip to: 4397
/* 4387 */    MCD::OPC_CheckField, 0, 2, 2, 14, 20, // Skip to: 9527
/* 4393 */    MCD::OPC_Decode, 139, 5, 61, // Opcode: LSWI
/* 4397 */    MCD::OPC_FilterValue, 20, 10, 0, // Skip to: 4411
/* 4401 */    MCD::OPC_CheckField, 0, 2, 0, 0, 20, // Skip to: 9527
/* 4407 */    MCD::OPC_Decode, 231, 6, 58, // Opcode: STDBRX
/* 4411 */    MCD::OPC_FilterValue, 22, 10, 0, // Skip to: 4425
/* 4415 */    MCD::OPC_CheckField, 0, 2, 2, 242, 19, // Skip to: 9527
/* 4421 */    MCD::OPC_Decode, 129, 7, 61, // Opcode: STSWI
/* 4425 */    MCD::OPC_FilterValue, 24, 10, 0, // Skip to: 4439
/* 4429 */    MCD::OPC_CheckField, 0, 2, 2, 228, 19, // Skip to: 9527
/* 4435 */    MCD::OPC_Decode, 157, 5, 42, // Opcode: LWZCIX
/* 4439 */    MCD::OPC_FilterValue, 25, 10, 0, // Skip to: 4453
/* 4443 */    MCD::OPC_CheckField, 0, 2, 2, 214, 19, // Skip to: 9527
/* 4449 */    MCD::OPC_Decode, 255, 4, 42, // Opcode: LHZCIX
/* 4453 */    MCD::OPC_FilterValue, 26, 10, 0, // Skip to: 4467
/* 4457 */    MCD::OPC_CheckField, 0, 2, 2, 200, 19, // Skip to: 9527
/* 4463 */    MCD::OPC_Decode, 211, 4, 42, // Opcode: LBZCIX
/* 4467 */    MCD::OPC_FilterValue, 27, 10, 0, // Skip to: 4481
/* 4471 */    MCD::OPC_CheckField, 0, 2, 2, 186, 19, // Skip to: 9527
/* 4477 */    MCD::OPC_Decode, 221, 4, 42, // Opcode: LDCIX
/* 4481 */    MCD::OPC_FilterValue, 28, 10, 0, // Skip to: 4495
/* 4485 */    MCD::OPC_CheckField, 0, 2, 2, 172, 19, // Skip to: 9527
/* 4491 */    MCD::OPC_Decode, 138, 7, 42, // Opcode: STWCIX
/* 4495 */    MCD::OPC_FilterValue, 29, 10, 0, // Skip to: 4509
/* 4499 */    MCD::OPC_CheckField, 0, 2, 2, 158, 19, // Skip to: 9527
/* 4505 */    MCD::OPC_Decode, 249, 6, 42, // Opcode: STHCIX
/* 4509 */    MCD::OPC_FilterValue, 30, 10, 0, // Skip to: 4523
/* 4513 */    MCD::OPC_CheckField, 0, 2, 2, 144, 19, // Skip to: 9527
/* 4519 */    MCD::OPC_Decode, 223, 6, 42, // Opcode: STBCIX
/* 4523 */    MCD::OPC_FilterValue, 31, 136, 19, // Skip to: 9527
/* 4527 */    MCD::OPC_CheckField, 0, 2, 2, 130, 19, // Skip to: 9527
/* 4533 */    MCD::OPC_Decode, 232, 6, 42, // Opcode: STDCIX
/* 4537 */    MCD::OPC_FilterValue, 11, 227, 2, // Skip to: 5280
/* 4541 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 4544 */    MCD::OPC_FilterValue, 0, 25, 0, // Skip to: 4573
/* 4548 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4551 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 4565
/* 4555 */    MCD::OPC_CheckField, 25, 1, 0, 102, 19, // Skip to: 9527
/* 4561 */    MCD::OPC_Decode, 196, 4, 62, // Opcode: ICBT
/* 4565 */    MCD::OPC_FilterValue, 2, 94, 19, // Skip to: 9527
/* 4569 */    MCD::OPC_Decode, 162, 5, 57, // Opcode: LWZX
/* 4573 */    MCD::OPC_FilterValue, 1, 25, 0, // Skip to: 4602
/* 4577 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4580 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 4594
/* 4584 */    MCD::OPC_CheckField, 21, 5, 0, 73, 19, // Skip to: 9527
/* 4590 */    MCD::OPC_Decode, 243, 1, 63, // Opcode: DCBST
/* 4594 */    MCD::OPC_FilterValue, 2, 65, 19, // Skip to: 9527
/* 4598 */    MCD::OPC_Decode, 160, 5, 64, // Opcode: LWZUX
/* 4602 */    MCD::OPC_FilterValue, 2, 25, 0, // Skip to: 4631
/* 4606 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4609 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 4623
/* 4613 */    MCD::OPC_CheckField, 21, 5, 0, 44, 19, // Skip to: 9527
/* 4619 */    MCD::OPC_Decode, 241, 1, 63, // Opcode: DCBF
/* 4623 */    MCD::OPC_FilterValue, 2, 36, 19, // Skip to: 9527
/* 4627 */    MCD::OPC_Decode, 216, 4, 57, // Opcode: LBZX
/* 4631 */    MCD::OPC_FilterValue, 3, 10, 0, // Skip to: 4645
/* 4635 */    MCD::OPC_CheckField, 0, 2, 2, 22, 19, // Skip to: 9527
/* 4641 */    MCD::OPC_Decode, 214, 4, 64, // Opcode: LBZUX
/* 4645 */    MCD::OPC_FilterValue, 4, 19, 0, // Skip to: 4668
/* 4649 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4652 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 4660
/* 4656 */    MCD::OPC_Decode, 139, 7, 57, // Opcode: STWCX
/* 4660 */    MCD::OPC_FilterValue, 2, 255, 18, // Skip to: 9527
/* 4664 */    MCD::OPC_Decode, 144, 7, 57, // Opcode: STWX
/* 4668 */    MCD::OPC_FilterValue, 5, 10, 0, // Skip to: 4682
/* 4672 */    MCD::OPC_CheckField, 0, 2, 2, 241, 18, // Skip to: 9527
/* 4678 */    MCD::OPC_Decode, 142, 7, 65, // Opcode: STWUX
/* 4682 */    MCD::OPC_FilterValue, 6, 19, 0, // Skip to: 4705
/* 4686 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4689 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 4697
/* 4693 */    MCD::OPC_Decode, 233, 6, 58, // Opcode: STDCX
/* 4697 */    MCD::OPC_FilterValue, 2, 218, 18, // Skip to: 9527
/* 4701 */    MCD::OPC_Decode, 228, 6, 57, // Opcode: STBX
/* 4705 */    MCD::OPC_FilterValue, 7, 25, 0, // Skip to: 4734
/* 4709 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4712 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 4726
/* 4716 */    MCD::OPC_CheckField, 21, 5, 0, 197, 18, // Skip to: 9527
/* 4722 */    MCD::OPC_Decode, 245, 1, 63, // Opcode: DCBTST
/* 4726 */    MCD::OPC_FilterValue, 2, 189, 18, // Skip to: 9527
/* 4730 */    MCD::OPC_Decode, 226, 6, 65, // Opcode: STBUX
/* 4734 */    MCD::OPC_FilterValue, 8, 25, 0, // Skip to: 4763
/* 4738 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4741 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 4755
/* 4745 */    MCD::OPC_CheckField, 21, 5, 0, 168, 18, // Skip to: 9527
/* 4751 */    MCD::OPC_Decode, 244, 1, 63, // Opcode: DCBT
/* 4755 */    MCD::OPC_FilterValue, 2, 160, 18, // Skip to: 9527
/* 4759 */    MCD::OPC_Decode, 132, 5, 57, // Opcode: LHZX
/* 4763 */    MCD::OPC_FilterValue, 9, 10, 0, // Skip to: 4777
/* 4767 */    MCD::OPC_CheckField, 0, 2, 2, 146, 18, // Skip to: 9527
/* 4773 */    MCD::OPC_Decode, 130, 5, 64, // Opcode: LHZUX
/* 4777 */    MCD::OPC_FilterValue, 10, 34, 0, // Skip to: 4815
/* 4781 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4784 */    MCD::OPC_FilterValue, 0, 19, 0, // Skip to: 4807
/* 4788 */    MCD::OPC_ExtractField, 23, 3,  // Inst{25-23} ...
/* 4791 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 4799
/* 4795 */    MCD::OPC_Decode, 131, 2, 66, // Opcode: DST
/* 4799 */    MCD::OPC_FilterValue, 4, 116, 18, // Skip to: 9527
/* 4803 */    MCD::OPC_Decode, 137, 2, 66, // Opcode: DSTT
/* 4807 */    MCD::OPC_FilterValue, 2, 108, 18, // Skip to: 9527
/* 4811 */    MCD::OPC_Decode, 249, 4, 57, // Opcode: LHAX
/* 4815 */    MCD::OPC_FilterValue, 11, 34, 0, // Skip to: 4853
/* 4819 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4822 */    MCD::OPC_FilterValue, 0, 19, 0, // Skip to: 4845
/* 4826 */    MCD::OPC_ExtractField, 23, 3,  // Inst{25-23} ...
/* 4829 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 4837
/* 4833 */    MCD::OPC_Decode, 133, 2, 66, // Opcode: DSTST
/* 4837 */    MCD::OPC_FilterValue, 4, 78, 18, // Skip to: 9527
/* 4841 */    MCD::OPC_Decode, 135, 2, 66, // Opcode: DSTSTT
/* 4845 */    MCD::OPC_FilterValue, 2, 70, 18, // Skip to: 9527
/* 4849 */    MCD::OPC_Decode, 247, 4, 64, // Opcode: LHAUX
/* 4853 */    MCD::OPC_FilterValue, 12, 10, 0, // Skip to: 4867
/* 4857 */    MCD::OPC_CheckField, 0, 2, 2, 56, 18, // Skip to: 9527
/* 4863 */    MCD::OPC_Decode, 254, 6, 57, // Opcode: STHX
/* 4867 */    MCD::OPC_FilterValue, 13, 10, 0, // Skip to: 4881
/* 4871 */    MCD::OPC_CheckField, 0, 2, 2, 42, 18, // Skip to: 9527
/* 4877 */    MCD::OPC_Decode, 252, 6, 65, // Opcode: STHUX
/* 4881 */    MCD::OPC_FilterValue, 14, 16, 0, // Skip to: 4901
/* 4885 */    MCD::OPC_CheckField, 21, 5, 0, 28, 18, // Skip to: 9527
/* 4891 */    MCD::OPC_CheckField, 0, 2, 0, 22, 18, // Skip to: 9527
/* 4897 */    MCD::OPC_Decode, 242, 1, 63, // Opcode: DCBI
/* 4901 */    MCD::OPC_FilterValue, 16, 19, 0, // Skip to: 4924
/* 4905 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4908 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 4916
/* 4912 */    MCD::OPC_Decode, 153, 5, 57, // Opcode: LWBRX
/* 4916 */    MCD::OPC_FilterValue, 2, 255, 17, // Skip to: 9527
/* 4920 */    MCD::OPC_Decode, 242, 4, 67, // Opcode: LFSX
/* 4924 */    MCD::OPC_FilterValue, 17, 25, 0, // Skip to: 4953
/* 4928 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4931 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 4945
/* 4935 */    MCD::OPC_CheckField, 11, 15, 0, 234, 17, // Skip to: 9527
/* 4941 */    MCD::OPC_Decode, 201, 7, 0, // Opcode: TLBSYNC
/* 4945 */    MCD::OPC_FilterValue, 2, 226, 17, // Skip to: 9527
/* 4949 */    MCD::OPC_Decode, 241, 4, 68, // Opcode: LFSUX
/* 4953 */    MCD::OPC_FilterValue, 18, 31, 0, // Skip to: 4988
/* 4957 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 4960 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 4980
/* 4964 */    MCD::OPC_CheckField, 23, 3, 0, 205, 17, // Skip to: 9527
/* 4970 */    MCD::OPC_CheckField, 11, 10, 0, 199, 17, // Skip to: 9527
/* 4976 */    MCD::OPC_Decode, 175, 7, 69, // Opcode: SYNC
/* 4980 */    MCD::OPC_FilterValue, 2, 191, 17, // Skip to: 9527
/* 4984 */    MCD::OPC_Decode, 236, 4, 70, // Opcode: LFDX
/* 4988 */    MCD::OPC_FilterValue, 19, 10, 0, // Skip to: 5002
/* 4992 */    MCD::OPC_CheckField, 0, 2, 2, 177, 17, // Skip to: 9527
/* 4998 */    MCD::OPC_Decode, 235, 4, 71, // Opcode: LFDUX
/* 5002 */    MCD::OPC_FilterValue, 20, 19, 0, // Skip to: 5025
/* 5006 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5009 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5017
/* 5013 */    MCD::OPC_Decode, 137, 7, 57, // Opcode: STWBRX
/* 5017 */    MCD::OPC_FilterValue, 2, 154, 17, // Skip to: 9527
/* 5021 */    MCD::OPC_Decode, 245, 6, 67, // Opcode: STFSX
/* 5025 */    MCD::OPC_FilterValue, 21, 10, 0, // Skip to: 5039
/* 5029 */    MCD::OPC_CheckField, 0, 2, 2, 140, 17, // Skip to: 9527
/* 5035 */    MCD::OPC_Decode, 244, 6, 72, // Opcode: STFSUX
/* 5039 */    MCD::OPC_FilterValue, 22, 10, 0, // Skip to: 5053
/* 5043 */    MCD::OPC_CheckField, 0, 2, 2, 126, 17, // Skip to: 9527
/* 5049 */    MCD::OPC_Decode, 240, 6, 70, // Opcode: STFDX
/* 5053 */    MCD::OPC_FilterValue, 23, 25, 0, // Skip to: 5082
/* 5057 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5060 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5074
/* 5064 */    MCD::OPC_CheckField, 21, 5, 0, 105, 17, // Skip to: 9527
/* 5070 */    MCD::OPC_Decode, 240, 1, 63, // Opcode: DCBA
/* 5074 */    MCD::OPC_FilterValue, 2, 97, 17, // Skip to: 9527
/* 5078 */    MCD::OPC_Decode, 239, 6, 73, // Opcode: STFDUX
/* 5082 */    MCD::OPC_FilterValue, 24, 10, 0, // Skip to: 5096
/* 5086 */    MCD::OPC_CheckField, 0, 2, 0, 83, 17, // Skip to: 9527
/* 5092 */    MCD::OPC_Decode, 251, 4, 57, // Opcode: LHBRX
/* 5096 */    MCD::OPC_FilterValue, 25, 43, 0, // Skip to: 5143
/* 5100 */    MCD::OPC_ExtractField, 23, 3,  // Inst{25-23} ...
/* 5103 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 5123
/* 5107 */    MCD::OPC_CheckField, 11, 10, 0, 62, 17, // Skip to: 9527
/* 5113 */    MCD::OPC_CheckField, 0, 2, 0, 56, 17, // Skip to: 9527
/* 5119 */    MCD::OPC_Decode, 129, 2, 74, // Opcode: DSS
/* 5123 */    MCD::OPC_FilterValue, 4, 48, 17, // Skip to: 9527
/* 5127 */    MCD::OPC_CheckField, 11, 12, 0, 42, 17, // Skip to: 9527
/* 5133 */    MCD::OPC_CheckField, 0, 2, 0, 36, 17, // Skip to: 9527
/* 5139 */    MCD::OPC_Decode, 130, 2, 0, // Opcode: DSSALL
/* 5143 */    MCD::OPC_FilterValue, 26, 41, 0, // Skip to: 5188
/* 5147 */    MCD::OPC_ExtractField, 1, 1,  // Inst{1} ...
/* 5150 */    MCD::OPC_FilterValue, 0, 20, 0, // Skip to: 5174
/* 5154 */    MCD::OPC_CheckField, 11, 15, 0, 10, 0, // Skip to: 5170
/* 5160 */    MCD::OPC_CheckField, 0, 1, 0, 4, 0, // Skip to: 5170
/* 5166 */    MCD::OPC_Decode, 215, 3, 0, // Opcode: EnforceIEIO
/* 5170 */    MCD::OPC_Decode, 169, 5, 75, // Opcode: MBAR
/* 5174 */    MCD::OPC_FilterValue, 1, 253, 16, // Skip to: 9527
/* 5178 */    MCD::OPC_CheckField, 0, 1, 0, 247, 16, // Skip to: 9527
/* 5184 */    MCD::OPC_Decode, 237, 4, 70, // Opcode: LFIWAX
/* 5188 */    MCD::OPC_FilterValue, 27, 10, 0, // Skip to: 5202
/* 5192 */    MCD::OPC_CheckField, 0, 2, 2, 233, 16, // Skip to: 9527
/* 5198 */    MCD::OPC_Decode, 238, 4, 70, // Opcode: LFIWZX
/* 5202 */    MCD::OPC_FilterValue, 28, 10, 0, // Skip to: 5216
/* 5206 */    MCD::OPC_CheckField, 0, 2, 0, 219, 16, // Skip to: 9527
/* 5212 */    MCD::OPC_Decode, 248, 6, 57, // Opcode: STHBRX
/* 5216 */    MCD::OPC_FilterValue, 30, 25, 0, // Skip to: 5245
/* 5220 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5223 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5237
/* 5227 */    MCD::OPC_CheckField, 21, 5, 0, 198, 16, // Skip to: 9527
/* 5233 */    MCD::OPC_Decode, 195, 4, 63, // Opcode: ICBI
/* 5237 */    MCD::OPC_FilterValue, 2, 190, 16, // Skip to: 9527
/* 5241 */    MCD::OPC_Decode, 241, 6, 70, // Opcode: STFIWX
/* 5245 */    MCD::OPC_FilterValue, 31, 182, 16, // Skip to: 9527
/* 5249 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 5252 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5266
/* 5256 */    MCD::OPC_CheckField, 0, 2, 0, 169, 16, // Skip to: 9527
/* 5262 */    MCD::OPC_Decode, 246, 1, 63, // Opcode: DCBZ
/* 5266 */    MCD::OPC_FilterValue, 1, 161, 16, // Skip to: 9527
/* 5270 */    MCD::OPC_CheckField, 0, 2, 0, 155, 16, // Skip to: 9527
/* 5276 */    MCD::OPC_Decode, 247, 1, 63, // Opcode: DCBZL
/* 5280 */    MCD::OPC_FilterValue, 12, 95, 0, // Skip to: 5379
/* 5284 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 5287 */    MCD::OPC_FilterValue, 0, 19, 0, // Skip to: 5310
/* 5291 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5294 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5302
/* 5298 */    MCD::OPC_Decode, 194, 6, 76, // Opcode: SLW
/* 5302 */    MCD::OPC_FilterValue, 1, 125, 16, // Skip to: 9527
/* 5306 */    MCD::OPC_Decode, 199, 6, 76, // Opcode: SLWo
/* 5310 */    MCD::OPC_FilterValue, 16, 19, 0, // Skip to: 5333
/* 5314 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5317 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5325
/* 5321 */    MCD::OPC_Decode, 215, 6, 76, // Opcode: SRW
/* 5325 */    MCD::OPC_FilterValue, 1, 102, 16, // Skip to: 9527
/* 5329 */    MCD::OPC_Decode, 220, 6, 76, // Opcode: SRWo
/* 5333 */    MCD::OPC_FilterValue, 24, 19, 0, // Skip to: 5356
/* 5337 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5340 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5348
/* 5344 */    MCD::OPC_Decode, 207, 6, 76, // Opcode: SRAW
/* 5348 */    MCD::OPC_FilterValue, 1, 79, 16, // Skip to: 9527
/* 5352 */    MCD::OPC_Decode, 210, 6, 76, // Opcode: SRAWo
/* 5356 */    MCD::OPC_FilterValue, 25, 71, 16, // Skip to: 9527
/* 5360 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5363 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5371
/* 5367 */    MCD::OPC_Decode, 208, 6, 77, // Opcode: SRAWI
/* 5371 */    MCD::OPC_FilterValue, 1, 56, 16, // Skip to: 9527
/* 5375 */    MCD::OPC_Decode, 209, 6, 77, // Opcode: SRAWIo
/* 5379 */    MCD::OPC_FilterValue, 13, 47, 1, // Skip to: 5686
/* 5383 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 5386 */    MCD::OPC_FilterValue, 0, 47, 0, // Skip to: 5437
/* 5390 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5393 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5407
/* 5397 */    MCD::OPC_CheckField, 11, 5, 0, 28, 16, // Skip to: 9527
/* 5403 */    MCD::OPC_Decode, 224, 1, 78, // Opcode: CNTLZW
/* 5407 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 5421
/* 5411 */    MCD::OPC_CheckField, 11, 5, 0, 14, 16, // Skip to: 9527
/* 5417 */    MCD::OPC_Decode, 227, 1, 78, // Opcode: CNTLZWo
/* 5421 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 5429
/* 5425 */    MCD::OPC_Decode, 190, 6, 79, // Opcode: SLD
/* 5429 */    MCD::OPC_FilterValue, 3, 254, 15, // Skip to: 9527
/* 5433 */    MCD::OPC_Decode, 193, 6, 79, // Opcode: SLDo
/* 5437 */    MCD::OPC_FilterValue, 1, 31, 0, // Skip to: 5472
/* 5441 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5444 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5458
/* 5448 */    MCD::OPC_CheckField, 11, 5, 0, 233, 15, // Skip to: 9527
/* 5454 */    MCD::OPC_Decode, 222, 1, 80, // Opcode: CNTLZD
/* 5458 */    MCD::OPC_FilterValue, 1, 225, 15, // Skip to: 9527
/* 5462 */    MCD::OPC_CheckField, 11, 5, 0, 219, 15, // Skip to: 9527
/* 5468 */    MCD::OPC_Decode, 223, 1, 80, // Opcode: CNTLZDo
/* 5472 */    MCD::OPC_FilterValue, 11, 16, 0, // Skip to: 5492
/* 5476 */    MCD::OPC_CheckField, 11, 5, 0, 205, 15, // Skip to: 9527
/* 5482 */    MCD::OPC_CheckField, 0, 2, 0, 199, 15, // Skip to: 9527
/* 5488 */    MCD::OPC_Decode, 130, 6, 78, // Opcode: POPCNTW
/* 5492 */    MCD::OPC_FilterValue, 15, 16, 0, // Skip to: 5512
/* 5496 */    MCD::OPC_CheckField, 11, 5, 0, 185, 15, // Skip to: 9527
/* 5502 */    MCD::OPC_CheckField, 0, 2, 0, 179, 15, // Skip to: 9527
/* 5508 */    MCD::OPC_Decode, 129, 6, 80, // Opcode: POPCNTD
/* 5512 */    MCD::OPC_FilterValue, 16, 19, 0, // Skip to: 5535
/* 5516 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5519 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 5527
/* 5523 */    MCD::OPC_Decode, 211, 6, 79, // Opcode: SRD
/* 5527 */    MCD::OPC_FilterValue, 3, 156, 15, // Skip to: 9527
/* 5531 */    MCD::OPC_Decode, 214, 6, 79, // Opcode: SRDo
/* 5535 */    MCD::OPC_FilterValue, 24, 19, 0, // Skip to: 5558
/* 5539 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5542 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5550
/* 5546 */    MCD::OPC_Decode, 203, 6, 79, // Opcode: SRAD
/* 5550 */    MCD::OPC_FilterValue, 1, 133, 15, // Skip to: 9527
/* 5554 */    MCD::OPC_Decode, 206, 6, 79, // Opcode: SRADo
/* 5558 */    MCD::OPC_FilterValue, 25, 19, 0, // Skip to: 5581
/* 5562 */    MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 5565 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5573
/* 5569 */    MCD::OPC_Decode, 204, 6, 81, // Opcode: SRADI
/* 5573 */    MCD::OPC_FilterValue, 1, 110, 15, // Skip to: 9527
/* 5577 */    MCD::OPC_Decode, 205, 6, 81, // Opcode: SRADIo
/* 5581 */    MCD::OPC_FilterValue, 28, 31, 0, // Skip to: 5616
/* 5585 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5588 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5602
/* 5592 */    MCD::OPC_CheckField, 11, 5, 0, 89, 15, // Skip to: 9527
/* 5598 */    MCD::OPC_Decode, 206, 3, 78, // Opcode: EXTSH
/* 5602 */    MCD::OPC_FilterValue, 1, 81, 15, // Skip to: 9527
/* 5606 */    MCD::OPC_CheckField, 11, 5, 0, 75, 15, // Skip to: 9527
/* 5612 */    MCD::OPC_Decode, 210, 3, 78, // Opcode: EXTSHo
/* 5616 */    MCD::OPC_FilterValue, 29, 31, 0, // Skip to: 5651
/* 5620 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5623 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5637
/* 5627 */    MCD::OPC_CheckField, 11, 5, 0, 54, 15, // Skip to: 9527
/* 5633 */    MCD::OPC_Decode, 201, 3, 78, // Opcode: EXTSB
/* 5637 */    MCD::OPC_FilterValue, 1, 46, 15, // Skip to: 9527
/* 5641 */    MCD::OPC_CheckField, 11, 5, 0, 40, 15, // Skip to: 9527
/* 5647 */    MCD::OPC_Decode, 205, 3, 78, // Opcode: EXTSBo
/* 5651 */    MCD::OPC_FilterValue, 30, 32, 15, // Skip to: 9527
/* 5655 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5658 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 5672
/* 5662 */    MCD::OPC_CheckField, 11, 5, 0, 19, 15, // Skip to: 9527
/* 5668 */    MCD::OPC_Decode, 211, 3, 80, // Opcode: EXTSW
/* 5672 */    MCD::OPC_FilterValue, 1, 11, 15, // Skip to: 9527
/* 5676 */    MCD::OPC_CheckField, 11, 5, 0, 5, 15, // Skip to: 9527
/* 5682 */    MCD::OPC_Decode, 214, 3, 80, // Opcode: EXTSWo
/* 5686 */    MCD::OPC_FilterValue, 14, 197, 0, // Skip to: 5887
/* 5690 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 5693 */    MCD::OPC_FilterValue, 0, 17, 0, // Skip to: 5714
/* 5697 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5700 */    MCD::OPC_FilterValue, 0, 3, 0, // Skip to: 5707
/* 5704 */    MCD::OPC_Decode, 67, 76, // Opcode: AND
/* 5707 */    MCD::OPC_FilterValue, 1, 232, 14, // Skip to: 9527
/* 5711 */    MCD::OPC_Decode, 82, 76, // Opcode: ANDo
/* 5714 */    MCD::OPC_FilterValue, 1, 17, 0, // Skip to: 5735
/* 5718 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5721 */    MCD::OPC_FilterValue, 0, 3, 0, // Skip to: 5728
/* 5725 */    MCD::OPC_Decode, 70, 76, // Opcode: ANDC
/* 5728 */    MCD::OPC_FilterValue, 1, 211, 14, // Skip to: 9527
/* 5732 */    MCD::OPC_Decode, 73, 76, // Opcode: ANDCo
/* 5735 */    MCD::OPC_FilterValue, 3, 19, 0, // Skip to: 5758
/* 5739 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5742 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5750
/* 5746 */    MCD::OPC_Decode, 241, 5, 76, // Opcode: NOR
/* 5750 */    MCD::OPC_FilterValue, 1, 189, 14, // Skip to: 9527
/* 5754 */    MCD::OPC_Decode, 244, 5, 76, // Opcode: NORo
/* 5758 */    MCD::OPC_FilterValue, 8, 19, 0, // Skip to: 5781
/* 5762 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5765 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5773
/* 5769 */    MCD::OPC_Decode, 146, 2, 76, // Opcode: EQV
/* 5773 */    MCD::OPC_FilterValue, 1, 166, 14, // Skip to: 9527
/* 5777 */    MCD::OPC_Decode, 149, 2, 76, // Opcode: EQVo
/* 5781 */    MCD::OPC_FilterValue, 9, 19, 0, // Skip to: 5804
/* 5785 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5788 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5796
/* 5792 */    MCD::OPC_Decode, 249, 8, 76, // Opcode: XOR
/* 5796 */    MCD::OPC_FilterValue, 1, 143, 14, // Skip to: 9527
/* 5800 */    MCD::OPC_Decode, 128, 9, 76, // Opcode: XORo
/* 5804 */    MCD::OPC_FilterValue, 12, 19, 0, // Skip to: 5827
/* 5808 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5811 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5819
/* 5815 */    MCD::OPC_Decode, 248, 5, 76, // Opcode: ORC
/* 5819 */    MCD::OPC_FilterValue, 1, 120, 14, // Skip to: 9527
/* 5823 */    MCD::OPC_Decode, 251, 5, 76, // Opcode: ORCo
/* 5827 */    MCD::OPC_FilterValue, 13, 19, 0, // Skip to: 5850
/* 5831 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5834 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5842
/* 5838 */    MCD::OPC_Decode, 245, 5, 76, // Opcode: OR
/* 5842 */    MCD::OPC_FilterValue, 1, 97, 14, // Skip to: 9527
/* 5846 */    MCD::OPC_Decode, 128, 6, 76, // Opcode: ORo
/* 5850 */    MCD::OPC_FilterValue, 14, 19, 0, // Skip to: 5873
/* 5854 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 5857 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 5865
/* 5861 */    MCD::OPC_Decode, 230, 5, 76, // Opcode: NAND
/* 5865 */    MCD::OPC_FilterValue, 1, 74, 14, // Skip to: 9527
/* 5869 */    MCD::OPC_Decode, 233, 5, 76, // Opcode: NANDo
/* 5873 */    MCD::OPC_FilterValue, 15, 66, 14, // Skip to: 9527
/* 5877 */    MCD::OPC_CheckField, 0, 2, 0, 60, 14, // Skip to: 9527
/* 5883 */    MCD::OPC_Decode, 212, 1, 76, // Opcode: CMPB
/* 5887 */    MCD::OPC_FilterValue, 15, 52, 14, // Skip to: 9527
/* 5891 */    MCD::OPC_CheckField, 23, 3, 0, 46, 14, // Skip to: 9527
/* 5897 */    MCD::OPC_CheckField, 6, 15, 1, 40, 14, // Skip to: 9527
/* 5903 */    MCD::OPC_CheckField, 0, 2, 0, 34, 14, // Skip to: 9527
/* 5909 */    MCD::OPC_Decode, 246, 8, 69, // Opcode: WAIT
/* 5913 */    MCD::OPC_FilterValue, 32, 4, 0, // Skip to: 5921
/* 5917 */    MCD::OPC_Decode, 155, 5, 82, // Opcode: LWZ
/* 5921 */    MCD::OPC_FilterValue, 33, 4, 0, // Skip to: 5929
/* 5925 */    MCD::OPC_Decode, 158, 5, 82, // Opcode: LWZU
/* 5929 */    MCD::OPC_FilterValue, 34, 4, 0, // Skip to: 5937
/* 5933 */    MCD::OPC_Decode, 209, 4, 82, // Opcode: LBZ
/* 5937 */    MCD::OPC_FilterValue, 35, 4, 0, // Skip to: 5945
/* 5941 */    MCD::OPC_Decode, 212, 4, 82, // Opcode: LBZU
/* 5945 */    MCD::OPC_FilterValue, 36, 4, 0, // Skip to: 5953
/* 5949 */    MCD::OPC_Decode, 135, 7, 82, // Opcode: STW
/* 5953 */    MCD::OPC_FilterValue, 37, 4, 0, // Skip to: 5961
/* 5957 */    MCD::OPC_Decode, 140, 7, 82, // Opcode: STWU
/* 5961 */    MCD::OPC_FilterValue, 38, 4, 0, // Skip to: 5969
/* 5965 */    MCD::OPC_Decode, 221, 6, 82, // Opcode: STB
/* 5969 */    MCD::OPC_FilterValue, 39, 4, 0, // Skip to: 5977
/* 5973 */    MCD::OPC_Decode, 224, 6, 82, // Opcode: STBU
/* 5977 */    MCD::OPC_FilterValue, 40, 4, 0, // Skip to: 5985
/* 5981 */    MCD::OPC_Decode, 253, 4, 82, // Opcode: LHZ
/* 5985 */    MCD::OPC_FilterValue, 41, 4, 0, // Skip to: 5993
/* 5989 */    MCD::OPC_Decode, 128, 5, 82, // Opcode: LHZU
/* 5993 */    MCD::OPC_FilterValue, 42, 4, 0, // Skip to: 6001
/* 5997 */    MCD::OPC_Decode, 243, 4, 82, // Opcode: LHA
/* 6001 */    MCD::OPC_FilterValue, 43, 4, 0, // Skip to: 6009
/* 6005 */    MCD::OPC_Decode, 245, 4, 82, // Opcode: LHAU
/* 6009 */    MCD::OPC_FilterValue, 44, 4, 0, // Skip to: 6017
/* 6013 */    MCD::OPC_Decode, 246, 6, 82, // Opcode: STH
/* 6017 */    MCD::OPC_FilterValue, 45, 4, 0, // Skip to: 6025
/* 6021 */    MCD::OPC_Decode, 250, 6, 82, // Opcode: STHU
/* 6025 */    MCD::OPC_FilterValue, 46, 4, 0, // Skip to: 6033
/* 6029 */    MCD::OPC_Decode, 138, 5, 82, // Opcode: LMW
/* 6033 */    MCD::OPC_FilterValue, 47, 4, 0, // Skip to: 6041
/* 6037 */    MCD::OPC_Decode, 128, 7, 82, // Opcode: STMW
/* 6041 */    MCD::OPC_FilterValue, 48, 4, 0, // Skip to: 6049
/* 6045 */    MCD::OPC_Decode, 239, 4, 83, // Opcode: LFS
/* 6049 */    MCD::OPC_FilterValue, 49, 4, 0, // Skip to: 6057
/* 6053 */    MCD::OPC_Decode, 240, 4, 83, // Opcode: LFSU
/* 6057 */    MCD::OPC_FilterValue, 50, 4, 0, // Skip to: 6065
/* 6061 */    MCD::OPC_Decode, 233, 4, 84, // Opcode: LFD
/* 6065 */    MCD::OPC_FilterValue, 51, 4, 0, // Skip to: 6073
/* 6069 */    MCD::OPC_Decode, 234, 4, 84, // Opcode: LFDU
/* 6073 */    MCD::OPC_FilterValue, 52, 4, 0, // Skip to: 6081
/* 6077 */    MCD::OPC_Decode, 242, 6, 83, // Opcode: STFS
/* 6081 */    MCD::OPC_FilterValue, 53, 4, 0, // Skip to: 6089
/* 6085 */    MCD::OPC_Decode, 243, 6, 83, // Opcode: STFSU
/* 6089 */    MCD::OPC_FilterValue, 54, 4, 0, // Skip to: 6097
/* 6093 */    MCD::OPC_Decode, 237, 6, 84, // Opcode: STFD
/* 6097 */    MCD::OPC_FilterValue, 55, 4, 0, // Skip to: 6105
/* 6101 */    MCD::OPC_Decode, 238, 6, 84, // Opcode: STFDU
/* 6105 */    MCD::OPC_FilterValue, 58, 27, 0, // Skip to: 6136
/* 6109 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 6112 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6120
/* 6116 */    MCD::OPC_Decode, 218, 4, 85, // Opcode: LD
/* 6120 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 6128
/* 6124 */    MCD::OPC_Decode, 222, 4, 85, // Opcode: LDU
/* 6128 */    MCD::OPC_FilterValue, 2, 67, 13, // Skip to: 9527
/* 6132 */    MCD::OPC_Decode, 147, 5, 85, // Opcode: LWA
/* 6136 */    MCD::OPC_FilterValue, 59, 113, 1, // Skip to: 6509
/* 6140 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 6143 */    MCD::OPC_FilterValue, 28, 31, 0, // Skip to: 6178
/* 6147 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 6150 */    MCD::OPC_FilterValue, 26, 10, 0, // Skip to: 6164
/* 6154 */    MCD::OPC_CheckField, 16, 5, 0, 39, 13, // Skip to: 9527
/* 6160 */    MCD::OPC_Decode, 226, 3, 86, // Opcode: FCFIDS
/* 6164 */    MCD::OPC_FilterValue, 30, 31, 13, // Skip to: 9527
/* 6168 */    MCD::OPC_CheckField, 16, 5, 0, 25, 13, // Skip to: 9527
/* 6174 */    MCD::OPC_Decode, 229, 3, 86, // Opcode: FCFIDUS
/* 6178 */    MCD::OPC_FilterValue, 29, 31, 0, // Skip to: 6213
/* 6182 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 6185 */    MCD::OPC_FilterValue, 26, 10, 0, // Skip to: 6199
/* 6189 */    MCD::OPC_CheckField, 16, 5, 0, 4, 13, // Skip to: 9527
/* 6195 */    MCD::OPC_Decode, 227, 3, 86, // Opcode: FCFIDSo
/* 6199 */    MCD::OPC_FilterValue, 30, 252, 12, // Skip to: 9527
/* 6203 */    MCD::OPC_CheckField, 16, 5, 0, 246, 12, // Skip to: 9527
/* 6209 */    MCD::OPC_Decode, 230, 3, 86, // Opcode: FCFIDUSo
/* 6213 */    MCD::OPC_FilterValue, 36, 10, 0, // Skip to: 6227
/* 6217 */    MCD::OPC_CheckField, 6, 5, 0, 232, 12, // Skip to: 9527
/* 6223 */    MCD::OPC_Decode, 252, 3, 87, // Opcode: FDIVS
/* 6227 */    MCD::OPC_FilterValue, 37, 10, 0, // Skip to: 6241
/* 6231 */    MCD::OPC_CheckField, 6, 5, 0, 218, 12, // Skip to: 9527
/* 6237 */    MCD::OPC_Decode, 253, 3, 87, // Opcode: FDIVSo
/* 6241 */    MCD::OPC_FilterValue, 40, 10, 0, // Skip to: 6255
/* 6245 */    MCD::OPC_CheckField, 6, 5, 0, 204, 12, // Skip to: 9527
/* 6251 */    MCD::OPC_Decode, 192, 4, 87, // Opcode: FSUBS
/* 6255 */    MCD::OPC_FilterValue, 41, 10, 0, // Skip to: 6269
/* 6259 */    MCD::OPC_CheckField, 6, 5, 0, 190, 12, // Skip to: 9527
/* 6265 */    MCD::OPC_Decode, 193, 4, 87, // Opcode: FSUBSo
/* 6269 */    MCD::OPC_FilterValue, 42, 10, 0, // Skip to: 6283
/* 6273 */    MCD::OPC_CheckField, 6, 5, 0, 176, 12, // Skip to: 9527
/* 6279 */    MCD::OPC_Decode, 221, 3, 87, // Opcode: FADDS
/* 6283 */    MCD::OPC_FilterValue, 43, 10, 0, // Skip to: 6297
/* 6287 */    MCD::OPC_CheckField, 6, 5, 0, 162, 12, // Skip to: 9527
/* 6293 */    MCD::OPC_Decode, 222, 3, 87, // Opcode: FADDSo
/* 6297 */    MCD::OPC_FilterValue, 44, 16, 0, // Skip to: 6317
/* 6301 */    MCD::OPC_CheckField, 16, 5, 0, 148, 12, // Skip to: 9527
/* 6307 */    MCD::OPC_CheckField, 6, 5, 0, 142, 12, // Skip to: 9527
/* 6313 */    MCD::OPC_Decode, 188, 4, 88, // Opcode: FSQRTS
/* 6317 */    MCD::OPC_FilterValue, 45, 16, 0, // Skip to: 6337
/* 6321 */    MCD::OPC_CheckField, 16, 5, 0, 128, 12, // Skip to: 9527
/* 6327 */    MCD::OPC_CheckField, 6, 5, 0, 122, 12, // Skip to: 9527
/* 6333 */    MCD::OPC_Decode, 189, 4, 88, // Opcode: FSQRTSo
/* 6337 */    MCD::OPC_FilterValue, 48, 16, 0, // Skip to: 6357
/* 6341 */    MCD::OPC_CheckField, 16, 5, 0, 108, 12, // Skip to: 9527
/* 6347 */    MCD::OPC_CheckField, 6, 5, 0, 102, 12, // Skip to: 9527
/* 6353 */    MCD::OPC_Decode, 158, 4, 88, // Opcode: FRES
/* 6357 */    MCD::OPC_FilterValue, 49, 16, 0, // Skip to: 6377
/* 6361 */    MCD::OPC_CheckField, 16, 5, 0, 88, 12, // Skip to: 9527
/* 6367 */    MCD::OPC_CheckField, 6, 5, 0, 82, 12, // Skip to: 9527
/* 6373 */    MCD::OPC_Decode, 159, 4, 88, // Opcode: FRESo
/* 6377 */    MCD::OPC_FilterValue, 50, 10, 0, // Skip to: 6391
/* 6381 */    MCD::OPC_CheckField, 11, 5, 0, 68, 12, // Skip to: 9527
/* 6387 */    MCD::OPC_Decode, 138, 4, 89, // Opcode: FMULS
/* 6391 */    MCD::OPC_FilterValue, 51, 10, 0, // Skip to: 6405
/* 6395 */    MCD::OPC_CheckField, 11, 5, 0, 54, 12, // Skip to: 9527
/* 6401 */    MCD::OPC_Decode, 139, 4, 89, // Opcode: FMULSo
/* 6405 */    MCD::OPC_FilterValue, 52, 16, 0, // Skip to: 6425
/* 6409 */    MCD::OPC_CheckField, 16, 5, 0, 40, 12, // Skip to: 9527
/* 6415 */    MCD::OPC_CheckField, 6, 5, 0, 34, 12, // Skip to: 9527
/* 6421 */    MCD::OPC_Decode, 180, 4, 88, // Opcode: FRSQRTES
/* 6425 */    MCD::OPC_FilterValue, 53, 16, 0, // Skip to: 6445
/* 6429 */    MCD::OPC_CheckField, 16, 5, 0, 20, 12, // Skip to: 9527
/* 6435 */    MCD::OPC_CheckField, 6, 5, 0, 14, 12, // Skip to: 9527
/* 6441 */    MCD::OPC_Decode, 181, 4, 88, // Opcode: FRSQRTESo
/* 6445 */    MCD::OPC_FilterValue, 56, 4, 0, // Skip to: 6453
/* 6449 */    MCD::OPC_Decode, 134, 4, 90, // Opcode: FMSUBS
/* 6453 */    MCD::OPC_FilterValue, 57, 4, 0, // Skip to: 6461
/* 6457 */    MCD::OPC_Decode, 135, 4, 90, // Opcode: FMSUBSo
/* 6461 */    MCD::OPC_FilterValue, 58, 4, 0, // Skip to: 6469
/* 6465 */    MCD::OPC_Decode, 128, 4, 90, // Opcode: FMADDS
/* 6469 */    MCD::OPC_FilterValue, 59, 4, 0, // Skip to: 6477
/* 6473 */    MCD::OPC_Decode, 129, 4, 90, // Opcode: FMADDSo
/* 6477 */    MCD::OPC_FilterValue, 60, 4, 0, // Skip to: 6485
/* 6481 */    MCD::OPC_Decode, 154, 4, 90, // Opcode: FNMSUBS
/* 6485 */    MCD::OPC_FilterValue, 61, 4, 0, // Skip to: 6493
/* 6489 */    MCD::OPC_Decode, 155, 4, 90, // Opcode: FNMSUBSo
/* 6493 */    MCD::OPC_FilterValue, 62, 4, 0, // Skip to: 6501
/* 6497 */    MCD::OPC_Decode, 150, 4, 90, // Opcode: FNMADDS
/* 6501 */    MCD::OPC_FilterValue, 63, 206, 11, // Skip to: 9527
/* 6505 */    MCD::OPC_Decode, 151, 4, 90, // Opcode: FNMADDSo
/* 6509 */    MCD::OPC_FilterValue, 60, 250, 7, // Skip to: 8555
/* 6513 */    MCD::OPC_ExtractField, 4, 2,  // Inst{5-4} ...
/* 6516 */    MCD::OPC_FilterValue, 0, 16, 2, // Skip to: 7048
/* 6520 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 6523 */    MCD::OPC_FilterValue, 4, 19, 0, // Skip to: 6546
/* 6527 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6530 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6538
/* 6534 */    MCD::OPC_Decode, 130, 9, 91, // Opcode: XSADDDP
/* 6538 */    MCD::OPC_FilterValue, 1, 169, 11, // Skip to: 9527
/* 6542 */    MCD::OPC_Decode, 143, 9, 92, // Opcode: XSMADDADP
/* 6546 */    MCD::OPC_FilterValue, 5, 19, 0, // Skip to: 6569
/* 6550 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6553 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6561
/* 6557 */    MCD::OPC_Decode, 164, 9, 91, // Opcode: XSSUBDP
/* 6561 */    MCD::OPC_FilterValue, 1, 146, 11, // Skip to: 9527
/* 6565 */    MCD::OPC_Decode, 144, 9, 92, // Opcode: XSMADDMDP
/* 6569 */    MCD::OPC_FilterValue, 6, 19, 0, // Skip to: 6592
/* 6573 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6576 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6584
/* 6580 */    MCD::OPC_Decode, 149, 9, 91, // Opcode: XSMULDP
/* 6584 */    MCD::OPC_FilterValue, 1, 123, 11, // Skip to: 9527
/* 6588 */    MCD::OPC_Decode, 147, 9, 92, // Opcode: XSMSUBADP
/* 6592 */    MCD::OPC_FilterValue, 7, 19, 0, // Skip to: 6615
/* 6596 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6599 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6607
/* 6603 */    MCD::OPC_Decode, 142, 9, 91, // Opcode: XSDIVDP
/* 6607 */    MCD::OPC_FilterValue, 1, 100, 11, // Skip to: 9527
/* 6611 */    MCD::OPC_Decode, 148, 9, 92, // Opcode: XSMSUBMDP
/* 6615 */    MCD::OPC_FilterValue, 8, 19, 0, // Skip to: 6638
/* 6619 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6622 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6630
/* 6626 */    MCD::OPC_Decode, 170, 9, 93, // Opcode: XVADDSP
/* 6630 */    MCD::OPC_FilterValue, 1, 77, 11, // Skip to: 9527
/* 6634 */    MCD::OPC_Decode, 206, 9, 94, // Opcode: XVMADDASP
/* 6638 */    MCD::OPC_FilterValue, 9, 19, 0, // Skip to: 6661
/* 6642 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6645 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6653
/* 6649 */    MCD::OPC_Decode, 248, 9, 93, // Opcode: XVSUBSP
/* 6653 */    MCD::OPC_FilterValue, 1, 54, 11, // Skip to: 9527
/* 6657 */    MCD::OPC_Decode, 208, 9, 94, // Opcode: XVMADDMSP
/* 6661 */    MCD::OPC_FilterValue, 10, 19, 0, // Skip to: 6684
/* 6665 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6668 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6676
/* 6672 */    MCD::OPC_Decode, 218, 9, 93, // Opcode: XVMULSP
/* 6676 */    MCD::OPC_FilterValue, 1, 31, 11, // Skip to: 9527
/* 6680 */    MCD::OPC_Decode, 214, 9, 94, // Opcode: XVMSUBASP
/* 6684 */    MCD::OPC_FilterValue, 11, 19, 0, // Skip to: 6707
/* 6688 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6691 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6699
/* 6695 */    MCD::OPC_Decode, 204, 9, 93, // Opcode: XVDIVSP
/* 6699 */    MCD::OPC_FilterValue, 1, 8, 11, // Skip to: 9527
/* 6703 */    MCD::OPC_Decode, 216, 9, 94, // Opcode: XVMSUBMSP
/* 6707 */    MCD::OPC_FilterValue, 12, 19, 0, // Skip to: 6730
/* 6711 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6714 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6722
/* 6718 */    MCD::OPC_Decode, 169, 9, 93, // Opcode: XVADDDP
/* 6722 */    MCD::OPC_FilterValue, 1, 241, 10, // Skip to: 9527
/* 6726 */    MCD::OPC_Decode, 205, 9, 94, // Opcode: XVMADDADP
/* 6730 */    MCD::OPC_FilterValue, 13, 19, 0, // Skip to: 6753
/* 6734 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6737 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6745
/* 6741 */    MCD::OPC_Decode, 247, 9, 93, // Opcode: XVSUBDP
/* 6745 */    MCD::OPC_FilterValue, 1, 218, 10, // Skip to: 9527
/* 6749 */    MCD::OPC_Decode, 207, 9, 94, // Opcode: XVMADDMDP
/* 6753 */    MCD::OPC_FilterValue, 14, 19, 0, // Skip to: 6776
/* 6757 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6760 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6768
/* 6764 */    MCD::OPC_Decode, 217, 9, 93, // Opcode: XVMULDP
/* 6768 */    MCD::OPC_FilterValue, 1, 195, 10, // Skip to: 9527
/* 6772 */    MCD::OPC_Decode, 213, 9, 94, // Opcode: XVMSUBADP
/* 6776 */    MCD::OPC_FilterValue, 15, 19, 0, // Skip to: 6799
/* 6780 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6783 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6791
/* 6787 */    MCD::OPC_Decode, 203, 9, 93, // Opcode: XVDIVDP
/* 6791 */    MCD::OPC_FilterValue, 1, 172, 10, // Skip to: 9527
/* 6795 */    MCD::OPC_Decode, 215, 9, 94, // Opcode: XVMSUBMDP
/* 6799 */    MCD::OPC_FilterValue, 20, 19, 0, // Skip to: 6822
/* 6803 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6806 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6814
/* 6810 */    MCD::OPC_Decode, 145, 9, 91, // Opcode: XSMAXDP
/* 6814 */    MCD::OPC_FilterValue, 1, 149, 10, // Skip to: 9527
/* 6818 */    MCD::OPC_Decode, 152, 9, 92, // Opcode: XSNMADDADP
/* 6822 */    MCD::OPC_FilterValue, 21, 19, 0, // Skip to: 6845
/* 6826 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6829 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6837
/* 6833 */    MCD::OPC_Decode, 146, 9, 91, // Opcode: XSMINDP
/* 6837 */    MCD::OPC_FilterValue, 1, 126, 10, // Skip to: 9527
/* 6841 */    MCD::OPC_Decode, 153, 9, 92, // Opcode: XSNMADDMDP
/* 6845 */    MCD::OPC_FilterValue, 22, 19, 0, // Skip to: 6868
/* 6849 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6852 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6860
/* 6856 */    MCD::OPC_Decode, 133, 9, 91, // Opcode: XSCPSGNDP
/* 6860 */    MCD::OPC_FilterValue, 1, 103, 10, // Skip to: 9527
/* 6864 */    MCD::OPC_Decode, 154, 9, 92, // Opcode: XSNMSUBADP
/* 6868 */    MCD::OPC_FilterValue, 23, 10, 0, // Skip to: 6882
/* 6872 */    MCD::OPC_CheckField, 3, 1, 1, 89, 10, // Skip to: 9527
/* 6878 */    MCD::OPC_Decode, 155, 9, 92, // Opcode: XSNMSUBMDP
/* 6882 */    MCD::OPC_FilterValue, 24, 19, 0, // Skip to: 6905
/* 6886 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6889 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6897
/* 6893 */    MCD::OPC_Decode, 210, 9, 93, // Opcode: XVMAXSP
/* 6897 */    MCD::OPC_FilterValue, 1, 66, 10, // Skip to: 9527
/* 6901 */    MCD::OPC_Decode, 224, 9, 94, // Opcode: XVNMADDASP
/* 6905 */    MCD::OPC_FilterValue, 25, 19, 0, // Skip to: 6928
/* 6909 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6912 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6920
/* 6916 */    MCD::OPC_Decode, 212, 9, 93, // Opcode: XVMINSP
/* 6920 */    MCD::OPC_FilterValue, 1, 43, 10, // Skip to: 9527
/* 6924 */    MCD::OPC_Decode, 226, 9, 94, // Opcode: XVNMADDMSP
/* 6928 */    MCD::OPC_FilterValue, 26, 19, 0, // Skip to: 6951
/* 6932 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6935 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6943
/* 6939 */    MCD::OPC_Decode, 184, 9, 93, // Opcode: XVCPSGNSP
/* 6943 */    MCD::OPC_FilterValue, 1, 20, 10, // Skip to: 9527
/* 6947 */    MCD::OPC_Decode, 228, 9, 94, // Opcode: XVNMSUBASP
/* 6951 */    MCD::OPC_FilterValue, 27, 10, 0, // Skip to: 6965
/* 6955 */    MCD::OPC_CheckField, 3, 1, 1, 6, 10, // Skip to: 9527
/* 6961 */    MCD::OPC_Decode, 230, 9, 94, // Opcode: XVNMSUBMSP
/* 6965 */    MCD::OPC_FilterValue, 28, 19, 0, // Skip to: 6988
/* 6969 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6972 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 6980
/* 6976 */    MCD::OPC_Decode, 209, 9, 93, // Opcode: XVMAXDP
/* 6980 */    MCD::OPC_FilterValue, 1, 239, 9, // Skip to: 9527
/* 6984 */    MCD::OPC_Decode, 223, 9, 94, // Opcode: XVNMADDADP
/* 6988 */    MCD::OPC_FilterValue, 29, 19, 0, // Skip to: 7011
/* 6992 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 6995 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 7003
/* 6999 */    MCD::OPC_Decode, 211, 9, 93, // Opcode: XVMINDP
/* 7003 */    MCD::OPC_FilterValue, 1, 216, 9, // Skip to: 9527
/* 7007 */    MCD::OPC_Decode, 225, 9, 94, // Opcode: XVNMADDMDP
/* 7011 */    MCD::OPC_FilterValue, 30, 19, 0, // Skip to: 7034
/* 7015 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 7018 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 7026
/* 7022 */    MCD::OPC_Decode, 183, 9, 93, // Opcode: XVCPSGNDP
/* 7026 */    MCD::OPC_FilterValue, 1, 193, 9, // Skip to: 9527
/* 7030 */    MCD::OPC_Decode, 227, 9, 94, // Opcode: XVNMSUBADP
/* 7034 */    MCD::OPC_FilterValue, 31, 185, 9, // Skip to: 9527
/* 7038 */    MCD::OPC_CheckField, 3, 1, 1, 179, 9, // Skip to: 9527
/* 7044 */    MCD::OPC_Decode, 229, 9, 94, // Opcode: XVNMSUBMDP
/* 7048 */    MCD::OPC_FilterValue, 1, 92, 1, // Skip to: 7400
/* 7052 */    MCD::OPC_ExtractField, 6, 2,  // Inst{7-6} ...
/* 7055 */    MCD::OPC_FilterValue, 0, 100, 0, // Skip to: 7159
/* 7059 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 7062 */    MCD::OPC_FilterValue, 0, 34, 0, // Skip to: 7100
/* 7066 */    MCD::OPC_ExtractField, 10, 1,  // Inst{10} ...
/* 7069 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 7077
/* 7073 */    MCD::OPC_Decode, 135, 10, 95, // Opcode: XXSLDWI
/* 7077 */    MCD::OPC_FilterValue, 1, 142, 9, // Skip to: 9527
/* 7081 */    MCD::OPC_ExtractField, 8, 2,  // Inst{9-8} ...
/* 7084 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 7092
/* 7088 */    MCD::OPC_Decode, 253, 9, 93, // Opcode: XXLAND
/* 7092 */    MCD::OPC_FilterValue, 1, 127, 9, // Skip to: 9527
/* 7096 */    MCD::OPC_Decode, 255, 9, 93, // Opcode: XXLNOR
/* 7100 */    MCD::OPC_FilterValue, 1, 119, 9, // Skip to: 9527
/* 7104 */    MCD::OPC_ExtractField, 8, 3,  // Inst{10-8} ...
/* 7107 */    MCD::OPC_FilterValue, 1, 16, 0, // Skip to: 7127
/* 7111 */    MCD::OPC_CheckField, 21, 2, 0, 106, 9, // Skip to: 9527
/* 7117 */    MCD::OPC_CheckField, 0, 1, 0, 100, 9, // Skip to: 9527
/* 7123 */    MCD::OPC_Decode, 132, 9, 96, // Opcode: XSCMPUDP
/* 7127 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 7135
/* 7131 */    MCD::OPC_Decode, 173, 9, 93, // Opcode: XVCMPEQSP
/* 7135 */    MCD::OPC_FilterValue, 3, 4, 0, // Skip to: 7143
/* 7139 */    MCD::OPC_Decode, 171, 9, 93, // Opcode: XVCMPEQDP
/* 7143 */    MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 7151
/* 7147 */    MCD::OPC_Decode, 174, 9, 93, // Opcode: XVCMPEQSPo
/* 7151 */    MCD::OPC_FilterValue, 7, 68, 9, // Skip to: 9527
/* 7155 */    MCD::OPC_Decode, 172, 9, 93, // Opcode: XVCMPEQDPo
/* 7159 */    MCD::OPC_FilterValue, 1, 91, 0, // Skip to: 7254
/* 7163 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 7166 */    MCD::OPC_FilterValue, 0, 25, 0, // Skip to: 7195
/* 7170 */    MCD::OPC_ExtractField, 10, 1,  // Inst{10} ...
/* 7173 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 7181
/* 7177 */    MCD::OPC_Decode, 133, 10, 95, // Opcode: XXPERMDI
/* 7181 */    MCD::OPC_FilterValue, 1, 38, 9, // Skip to: 9527
/* 7185 */    MCD::OPC_CheckField, 8, 2, 0, 32, 9, // Skip to: 9527
/* 7191 */    MCD::OPC_Decode, 254, 9, 93, // Opcode: XXLANDC
/* 7195 */    MCD::OPC_FilterValue, 1, 24, 9, // Skip to: 9527
/* 7199 */    MCD::OPC_ExtractField, 8, 3,  // Inst{10-8} ...
/* 7202 */    MCD::OPC_FilterValue, 1, 16, 0, // Skip to: 7222
/* 7206 */    MCD::OPC_CheckField, 21, 2, 0, 11, 9, // Skip to: 9527
/* 7212 */    MCD::OPC_CheckField, 0, 1, 0, 5, 9, // Skip to: 9527
/* 7218 */    MCD::OPC_Decode, 131, 9, 96, // Opcode: XSCMPODP
/* 7222 */    MCD::OPC_FilterValue, 2, 4, 0, // Skip to: 7230
/* 7226 */    MCD::OPC_Decode, 181, 9, 93, // Opcode: XVCMPGTSP
/* 7230 */    MCD::OPC_FilterValue, 3, 4, 0, // Skip to: 7238
/* 7234 */    MCD::OPC_Decode, 179, 9, 93, // Opcode: XVCMPGTDP
/* 7238 */    MCD::OPC_FilterValue, 6, 4, 0, // Skip to: 7246
/* 7242 */    MCD::OPC_Decode, 182, 9, 93, // Opcode: XVCMPGTSPo
/* 7246 */    MCD::OPC_FilterValue, 7, 229, 8, // Skip to: 9527
/* 7250 */    MCD::OPC_Decode, 180, 9, 93, // Opcode: XVCMPGTDPo
/* 7254 */    MCD::OPC_FilterValue, 2, 122, 0, // Skip to: 7380
/* 7258 */    MCD::OPC_ExtractField, 8, 3,  // Inst{10-8} ...
/* 7261 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7275
/* 7265 */    MCD::OPC_CheckField, 3, 1, 0, 208, 8, // Skip to: 9527
/* 7271 */    MCD::OPC_Decode, 131, 10, 93, // Opcode: XXMRGHW
/* 7275 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7289
/* 7279 */    MCD::OPC_CheckField, 3, 1, 0, 194, 8, // Skip to: 9527
/* 7285 */    MCD::OPC_Decode, 132, 10, 93, // Opcode: XXMRGLW
/* 7289 */    MCD::OPC_FilterValue, 2, 31, 0, // Skip to: 7324
/* 7293 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 7296 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 7316
/* 7300 */    MCD::OPC_CheckField, 18, 3, 0, 173, 8, // Skip to: 9527
/* 7306 */    MCD::OPC_CheckField, 2, 1, 0, 167, 8, // Skip to: 9527
/* 7312 */    MCD::OPC_Decode, 136, 10, 97, // Opcode: XXSPLTW
/* 7316 */    MCD::OPC_FilterValue, 1, 159, 8, // Skip to: 9527
/* 7320 */    MCD::OPC_Decode, 177, 9, 93, // Opcode: XVCMPGESP
/* 7324 */    MCD::OPC_FilterValue, 3, 10, 0, // Skip to: 7338
/* 7328 */    MCD::OPC_CheckField, 3, 1, 1, 145, 8, // Skip to: 9527
/* 7334 */    MCD::OPC_Decode, 175, 9, 93, // Opcode: XVCMPGEDP
/* 7338 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 7352
/* 7342 */    MCD::OPC_CheckField, 3, 1, 0, 131, 8, // Skip to: 9527
/* 7348 */    MCD::OPC_Decode, 128, 10, 93, // Opcode: XXLOR
/* 7352 */    MCD::OPC_FilterValue, 6, 10, 0, // Skip to: 7366
/* 7356 */    MCD::OPC_CheckField, 3, 1, 1, 117, 8, // Skip to: 9527
/* 7362 */    MCD::OPC_Decode, 178, 9, 93, // Opcode: XVCMPGESPo
/* 7366 */    MCD::OPC_FilterValue, 7, 109, 8, // Skip to: 9527
/* 7370 */    MCD::OPC_CheckField, 3, 1, 1, 103, 8, // Skip to: 9527
/* 7376 */    MCD::OPC_Decode, 176, 9, 93, // Opcode: XVCMPGEDPo
/* 7380 */    MCD::OPC_FilterValue, 3, 95, 8, // Skip to: 9527
/* 7384 */    MCD::OPC_CheckField, 8, 3, 4, 89, 8, // Skip to: 9527
/* 7390 */    MCD::OPC_CheckField, 3, 1, 0, 83, 8, // Skip to: 9527
/* 7396 */    MCD::OPC_Decode, 130, 10, 93, // Opcode: XXLXOR
/* 7400 */    MCD::OPC_FilterValue, 2, 119, 4, // Skip to: 8547
/* 7404 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 7407 */    MCD::OPC_FilterValue, 4, 59, 0, // Skip to: 7470
/* 7411 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7414 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7428
/* 7418 */    MCD::OPC_CheckField, 16, 5, 0, 55, 8, // Skip to: 9527
/* 7424 */    MCD::OPC_Decode, 138, 9, 98, // Opcode: XSCVDPUXWS
/* 7428 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7442
/* 7432 */    MCD::OPC_CheckField, 16, 5, 0, 41, 8, // Skip to: 9527
/* 7438 */    MCD::OPC_Decode, 156, 9, 98, // Opcode: XSRDPI
/* 7442 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 7456
/* 7446 */    MCD::OPC_CheckField, 16, 5, 0, 27, 8, // Skip to: 9527
/* 7452 */    MCD::OPC_Decode, 162, 9, 98, // Opcode: XSRSQRTEDP
/* 7456 */    MCD::OPC_FilterValue, 3, 19, 8, // Skip to: 9527
/* 7460 */    MCD::OPC_CheckField, 16, 5, 0, 13, 8, // Skip to: 9527
/* 7466 */    MCD::OPC_Decode, 163, 9, 98, // Opcode: XSSQRTDP
/* 7470 */    MCD::OPC_FilterValue, 5, 45, 0, // Skip to: 7519
/* 7474 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7477 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7491
/* 7481 */    MCD::OPC_CheckField, 16, 5, 0, 248, 7, // Skip to: 9527
/* 7487 */    MCD::OPC_Decode, 136, 9, 98, // Opcode: XSCVDPSXWS
/* 7491 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7505
/* 7495 */    MCD::OPC_CheckField, 16, 5, 0, 234, 7, // Skip to: 9527
/* 7501 */    MCD::OPC_Decode, 160, 9, 98, // Opcode: XSRDPIZ
/* 7505 */    MCD::OPC_FilterValue, 2, 226, 7, // Skip to: 9527
/* 7509 */    MCD::OPC_CheckField, 16, 5, 0, 220, 7, // Skip to: 9527
/* 7515 */    MCD::OPC_Decode, 161, 9, 98, // Opcode: XSREDP
/* 7519 */    MCD::OPC_FilterValue, 6, 51, 0, // Skip to: 7574
/* 7523 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7526 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7540
/* 7530 */    MCD::OPC_CheckField, 16, 5, 0, 199, 7, // Skip to: 9527
/* 7536 */    MCD::OPC_Decode, 159, 9, 98, // Opcode: XSRDPIP
/* 7540 */    MCD::OPC_FilterValue, 2, 16, 0, // Skip to: 7560
/* 7544 */    MCD::OPC_CheckField, 16, 7, 0, 185, 7, // Skip to: 9527
/* 7550 */    MCD::OPC_CheckField, 0, 1, 0, 179, 7, // Skip to: 9527
/* 7556 */    MCD::OPC_Decode, 166, 9, 99, // Opcode: XSTSQRTDP
/* 7560 */    MCD::OPC_FilterValue, 3, 171, 7, // Skip to: 9527
/* 7564 */    MCD::OPC_CheckField, 16, 5, 0, 165, 7, // Skip to: 9527
/* 7570 */    MCD::OPC_Decode, 157, 9, 98, // Opcode: XSRDPIC
/* 7574 */    MCD::OPC_FilterValue, 7, 43, 0, // Skip to: 7621
/* 7578 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 7581 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 7601
/* 7585 */    MCD::OPC_CheckField, 16, 5, 0, 144, 7, // Skip to: 9527
/* 7591 */    MCD::OPC_CheckField, 2, 1, 1, 138, 7, // Skip to: 9527
/* 7597 */    MCD::OPC_Decode, 158, 9, 98, // Opcode: XSRDPIM
/* 7601 */    MCD::OPC_FilterValue, 1, 130, 7, // Skip to: 9527
/* 7605 */    MCD::OPC_CheckField, 21, 2, 0, 124, 7, // Skip to: 9527
/* 7611 */    MCD::OPC_CheckField, 0, 1, 0, 118, 7, // Skip to: 9527
/* 7617 */    MCD::OPC_Decode, 165, 9, 96, // Opcode: XSTDIVDP
/* 7621 */    MCD::OPC_FilterValue, 8, 59, 0, // Skip to: 7684
/* 7625 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7628 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7642
/* 7632 */    MCD::OPC_CheckField, 16, 5, 0, 97, 7, // Skip to: 9527
/* 7638 */    MCD::OPC_Decode, 194, 9, 100, // Opcode: XVCVSPUXWS
/* 7642 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7656
/* 7646 */    MCD::OPC_CheckField, 16, 5, 0, 83, 7, // Skip to: 9527
/* 7652 */    MCD::OPC_Decode, 238, 9, 100, // Opcode: XVRSPI
/* 7656 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 7670
/* 7660 */    MCD::OPC_CheckField, 16, 5, 0, 69, 7, // Skip to: 9527
/* 7666 */    MCD::OPC_Decode, 244, 9, 100, // Opcode: XVRSQRTESP
/* 7670 */    MCD::OPC_FilterValue, 3, 61, 7, // Skip to: 9527
/* 7674 */    MCD::OPC_CheckField, 16, 5, 0, 55, 7, // Skip to: 9527
/* 7680 */    MCD::OPC_Decode, 246, 9, 100, // Opcode: XVSQRTSP
/* 7684 */    MCD::OPC_FilterValue, 9, 45, 0, // Skip to: 7733
/* 7688 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7691 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7705
/* 7695 */    MCD::OPC_CheckField, 16, 5, 0, 34, 7, // Skip to: 9527
/* 7701 */    MCD::OPC_Decode, 192, 9, 100, // Opcode: XVCVSPSXWS
/* 7705 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7719
/* 7709 */    MCD::OPC_CheckField, 16, 5, 0, 20, 7, // Skip to: 9527
/* 7715 */    MCD::OPC_Decode, 242, 9, 100, // Opcode: XVRSPIZ
/* 7719 */    MCD::OPC_FilterValue, 2, 12, 7, // Skip to: 9527
/* 7723 */    MCD::OPC_CheckField, 16, 5, 0, 6, 7, // Skip to: 9527
/* 7729 */    MCD::OPC_Decode, 237, 9, 100, // Opcode: XVRESP
/* 7733 */    MCD::OPC_FilterValue, 10, 65, 0, // Skip to: 7802
/* 7737 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7740 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7754
/* 7744 */    MCD::OPC_CheckField, 16, 5, 0, 241, 6, // Skip to: 9527
/* 7750 */    MCD::OPC_Decode, 202, 9, 100, // Opcode: XVCVUXWSP
/* 7754 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7768
/* 7758 */    MCD::OPC_CheckField, 16, 5, 0, 227, 6, // Skip to: 9527
/* 7764 */    MCD::OPC_Decode, 241, 9, 100, // Opcode: XVRSPIP
/* 7768 */    MCD::OPC_FilterValue, 2, 16, 0, // Skip to: 7788
/* 7772 */    MCD::OPC_CheckField, 16, 7, 0, 213, 6, // Skip to: 9527
/* 7778 */    MCD::OPC_CheckField, 0, 1, 0, 207, 6, // Skip to: 9527
/* 7784 */    MCD::OPC_Decode, 252, 9, 101, // Opcode: XVTSQRTSP
/* 7788 */    MCD::OPC_FilterValue, 3, 199, 6, // Skip to: 9527
/* 7792 */    MCD::OPC_CheckField, 16, 5, 0, 193, 6, // Skip to: 9527
/* 7798 */    MCD::OPC_Decode, 239, 9, 100, // Opcode: XVRSPIC
/* 7802 */    MCD::OPC_FilterValue, 11, 58, 0, // Skip to: 7864
/* 7806 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 7809 */    MCD::OPC_FilterValue, 0, 31, 0, // Skip to: 7844
/* 7813 */    MCD::OPC_ExtractField, 2, 1,  // Inst{2} ...
/* 7816 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7830
/* 7820 */    MCD::OPC_CheckField, 16, 5, 0, 165, 6, // Skip to: 9527
/* 7826 */    MCD::OPC_Decode, 198, 9, 100, // Opcode: XVCVSXWSP
/* 7830 */    MCD::OPC_FilterValue, 1, 157, 6, // Skip to: 9527
/* 7834 */    MCD::OPC_CheckField, 16, 5, 0, 151, 6, // Skip to: 9527
/* 7840 */    MCD::OPC_Decode, 240, 9, 100, // Opcode: XVRSPIM
/* 7844 */    MCD::OPC_FilterValue, 1, 143, 6, // Skip to: 9527
/* 7848 */    MCD::OPC_CheckField, 21, 2, 0, 137, 6, // Skip to: 9527
/* 7854 */    MCD::OPC_CheckField, 0, 1, 0, 131, 6, // Skip to: 9527
/* 7860 */    MCD::OPC_Decode, 250, 9, 102, // Opcode: XVTDIVSP
/* 7864 */    MCD::OPC_FilterValue, 12, 59, 0, // Skip to: 7927
/* 7868 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7871 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7885
/* 7875 */    MCD::OPC_CheckField, 16, 5, 0, 110, 6, // Skip to: 9527
/* 7881 */    MCD::OPC_Decode, 189, 9, 100, // Opcode: XVCVDPUXWS
/* 7885 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7899
/* 7889 */    MCD::OPC_CheckField, 16, 5, 0, 96, 6, // Skip to: 9527
/* 7895 */    MCD::OPC_Decode, 231, 9, 100, // Opcode: XVRDPI
/* 7899 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 7913
/* 7903 */    MCD::OPC_CheckField, 16, 5, 0, 82, 6, // Skip to: 9527
/* 7909 */    MCD::OPC_Decode, 243, 9, 100, // Opcode: XVRSQRTEDP
/* 7913 */    MCD::OPC_FilterValue, 3, 74, 6, // Skip to: 9527
/* 7917 */    MCD::OPC_CheckField, 16, 5, 0, 68, 6, // Skip to: 9527
/* 7923 */    MCD::OPC_Decode, 245, 9, 100, // Opcode: XVSQRTDP
/* 7927 */    MCD::OPC_FilterValue, 13, 45, 0, // Skip to: 7976
/* 7931 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7934 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7948
/* 7938 */    MCD::OPC_CheckField, 16, 5, 0, 47, 6, // Skip to: 9527
/* 7944 */    MCD::OPC_Decode, 187, 9, 100, // Opcode: XVCVDPSXWS
/* 7948 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 7962
/* 7952 */    MCD::OPC_CheckField, 16, 5, 0, 33, 6, // Skip to: 9527
/* 7958 */    MCD::OPC_Decode, 235, 9, 100, // Opcode: XVRDPIZ
/* 7962 */    MCD::OPC_FilterValue, 2, 25, 6, // Skip to: 9527
/* 7966 */    MCD::OPC_CheckField, 16, 5, 0, 19, 6, // Skip to: 9527
/* 7972 */    MCD::OPC_Decode, 236, 9, 100, // Opcode: XVREDP
/* 7976 */    MCD::OPC_FilterValue, 14, 65, 0, // Skip to: 8045
/* 7980 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 7983 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 7997
/* 7987 */    MCD::OPC_CheckField, 16, 5, 0, 254, 5, // Skip to: 9527
/* 7993 */    MCD::OPC_Decode, 201, 9, 100, // Opcode: XVCVUXWDP
/* 7997 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 8011
/* 8001 */    MCD::OPC_CheckField, 16, 5, 0, 240, 5, // Skip to: 9527
/* 8007 */    MCD::OPC_Decode, 234, 9, 100, // Opcode: XVRDPIP
/* 8011 */    MCD::OPC_FilterValue, 2, 16, 0, // Skip to: 8031
/* 8015 */    MCD::OPC_CheckField, 16, 7, 0, 226, 5, // Skip to: 9527
/* 8021 */    MCD::OPC_CheckField, 0, 1, 0, 220, 5, // Skip to: 9527
/* 8027 */    MCD::OPC_Decode, 251, 9, 101, // Opcode: XVTSQRTDP
/* 8031 */    MCD::OPC_FilterValue, 3, 212, 5, // Skip to: 9527
/* 8035 */    MCD::OPC_CheckField, 16, 5, 0, 206, 5, // Skip to: 9527
/* 8041 */    MCD::OPC_Decode, 232, 9, 100, // Opcode: XVRDPIC
/* 8045 */    MCD::OPC_FilterValue, 15, 58, 0, // Skip to: 8107
/* 8049 */    MCD::OPC_ExtractField, 3, 1,  // Inst{3} ...
/* 8052 */    MCD::OPC_FilterValue, 0, 31, 0, // Skip to: 8087
/* 8056 */    MCD::OPC_ExtractField, 2, 1,  // Inst{2} ...
/* 8059 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8073
/* 8063 */    MCD::OPC_CheckField, 16, 5, 0, 178, 5, // Skip to: 9527
/* 8069 */    MCD::OPC_Decode, 197, 9, 100, // Opcode: XVCVSXWDP
/* 8073 */    MCD::OPC_FilterValue, 1, 170, 5, // Skip to: 9527
/* 8077 */    MCD::OPC_CheckField, 16, 5, 0, 164, 5, // Skip to: 9527
/* 8083 */    MCD::OPC_Decode, 233, 9, 100, // Opcode: XVRDPIM
/* 8087 */    MCD::OPC_FilterValue, 1, 156, 5, // Skip to: 9527
/* 8091 */    MCD::OPC_CheckField, 21, 2, 0, 150, 5, // Skip to: 9527
/* 8097 */    MCD::OPC_CheckField, 0, 1, 0, 144, 5, // Skip to: 9527
/* 8103 */    MCD::OPC_Decode, 249, 9, 102, // Opcode: XVTDIVDP
/* 8107 */    MCD::OPC_FilterValue, 16, 16, 0, // Skip to: 8127
/* 8111 */    MCD::OPC_CheckField, 16, 5, 0, 130, 5, // Skip to: 9527
/* 8117 */    MCD::OPC_CheckField, 2, 2, 1, 124, 5, // Skip to: 9527
/* 8123 */    MCD::OPC_Decode, 134, 9, 98, // Opcode: XSCVDPSP
/* 8127 */    MCD::OPC_FilterValue, 20, 31, 0, // Skip to: 8162
/* 8131 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8134 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8148
/* 8138 */    MCD::OPC_CheckField, 16, 5, 0, 103, 5, // Skip to: 9527
/* 8144 */    MCD::OPC_Decode, 137, 9, 98, // Opcode: XSCVDPUXDS
/* 8148 */    MCD::OPC_FilterValue, 1, 95, 5, // Skip to: 9527
/* 8152 */    MCD::OPC_CheckField, 16, 5, 0, 89, 5, // Skip to: 9527
/* 8158 */    MCD::OPC_Decode, 139, 9, 98, // Opcode: XSCVSPDP
/* 8162 */    MCD::OPC_FilterValue, 21, 31, 0, // Skip to: 8197
/* 8166 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8169 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8183
/* 8173 */    MCD::OPC_CheckField, 16, 5, 0, 68, 5, // Skip to: 9527
/* 8179 */    MCD::OPC_Decode, 135, 9, 98, // Opcode: XSCVDPSXDS
/* 8183 */    MCD::OPC_FilterValue, 1, 60, 5, // Skip to: 9527
/* 8187 */    MCD::OPC_CheckField, 16, 5, 0, 54, 5, // Skip to: 9527
/* 8193 */    MCD::OPC_Decode, 129, 9, 98, // Opcode: XSABSDP
/* 8197 */    MCD::OPC_FilterValue, 22, 31, 0, // Skip to: 8232
/* 8201 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8204 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8218
/* 8208 */    MCD::OPC_CheckField, 16, 5, 0, 33, 5, // Skip to: 9527
/* 8214 */    MCD::OPC_Decode, 141, 9, 98, // Opcode: XSCVUXDDP
/* 8218 */    MCD::OPC_FilterValue, 1, 25, 5, // Skip to: 9527
/* 8222 */    MCD::OPC_CheckField, 16, 5, 0, 19, 5, // Skip to: 9527
/* 8228 */    MCD::OPC_Decode, 150, 9, 98, // Opcode: XSNABSDP
/* 8232 */    MCD::OPC_FilterValue, 23, 31, 0, // Skip to: 8267
/* 8236 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8239 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8253
/* 8243 */    MCD::OPC_CheckField, 16, 5, 0, 254, 4, // Skip to: 9527
/* 8249 */    MCD::OPC_Decode, 140, 9, 98, // Opcode: XSCVSXDDP
/* 8253 */    MCD::OPC_FilterValue, 1, 246, 4, // Skip to: 9527
/* 8257 */    MCD::OPC_CheckField, 16, 5, 0, 240, 4, // Skip to: 9527
/* 8263 */    MCD::OPC_Decode, 151, 9, 98, // Opcode: XSNEGDP
/* 8267 */    MCD::OPC_FilterValue, 24, 31, 0, // Skip to: 8302
/* 8271 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8274 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8288
/* 8278 */    MCD::OPC_CheckField, 16, 5, 0, 219, 4, // Skip to: 9527
/* 8284 */    MCD::OPC_Decode, 193, 9, 100, // Opcode: XVCVSPUXDS
/* 8288 */    MCD::OPC_FilterValue, 1, 211, 4, // Skip to: 9527
/* 8292 */    MCD::OPC_CheckField, 16, 5, 0, 205, 4, // Skip to: 9527
/* 8298 */    MCD::OPC_Decode, 185, 9, 100, // Opcode: XVCVDPSP
/* 8302 */    MCD::OPC_FilterValue, 25, 31, 0, // Skip to: 8337
/* 8306 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8309 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8323
/* 8313 */    MCD::OPC_CheckField, 16, 5, 0, 184, 4, // Skip to: 9527
/* 8319 */    MCD::OPC_Decode, 191, 9, 100, // Opcode: XVCVSPSXDS
/* 8323 */    MCD::OPC_FilterValue, 1, 176, 4, // Skip to: 9527
/* 8327 */    MCD::OPC_CheckField, 16, 5, 0, 170, 4, // Skip to: 9527
/* 8333 */    MCD::OPC_Decode, 168, 9, 100, // Opcode: XVABSSP
/* 8337 */    MCD::OPC_FilterValue, 26, 31, 0, // Skip to: 8372
/* 8341 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8344 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8358
/* 8348 */    MCD::OPC_CheckField, 16, 5, 0, 149, 4, // Skip to: 9527
/* 8354 */    MCD::OPC_Decode, 200, 9, 100, // Opcode: XVCVUXDSP
/* 8358 */    MCD::OPC_FilterValue, 1, 141, 4, // Skip to: 9527
/* 8362 */    MCD::OPC_CheckField, 16, 5, 0, 135, 4, // Skip to: 9527
/* 8368 */    MCD::OPC_Decode, 220, 9, 100, // Opcode: XVNABSSP
/* 8372 */    MCD::OPC_FilterValue, 27, 31, 0, // Skip to: 8407
/* 8376 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8379 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8393
/* 8383 */    MCD::OPC_CheckField, 16, 5, 0, 114, 4, // Skip to: 9527
/* 8389 */    MCD::OPC_Decode, 196, 9, 100, // Opcode: XVCVSXDSP
/* 8393 */    MCD::OPC_FilterValue, 1, 106, 4, // Skip to: 9527
/* 8397 */    MCD::OPC_CheckField, 16, 5, 0, 100, 4, // Skip to: 9527
/* 8403 */    MCD::OPC_Decode, 222, 9, 100, // Opcode: XVNEGSP
/* 8407 */    MCD::OPC_FilterValue, 28, 31, 0, // Skip to: 8442
/* 8411 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8414 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8428
/* 8418 */    MCD::OPC_CheckField, 16, 5, 0, 79, 4, // Skip to: 9527
/* 8424 */    MCD::OPC_Decode, 188, 9, 100, // Opcode: XVCVDPUXDS
/* 8428 */    MCD::OPC_FilterValue, 1, 71, 4, // Skip to: 9527
/* 8432 */    MCD::OPC_CheckField, 16, 5, 0, 65, 4, // Skip to: 9527
/* 8438 */    MCD::OPC_Decode, 190, 9, 100, // Opcode: XVCVSPDP
/* 8442 */    MCD::OPC_FilterValue, 29, 31, 0, // Skip to: 8477
/* 8446 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8449 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8463
/* 8453 */    MCD::OPC_CheckField, 16, 5, 0, 44, 4, // Skip to: 9527
/* 8459 */    MCD::OPC_Decode, 186, 9, 100, // Opcode: XVCVDPSXDS
/* 8463 */    MCD::OPC_FilterValue, 1, 36, 4, // Skip to: 9527
/* 8467 */    MCD::OPC_CheckField, 16, 5, 0, 30, 4, // Skip to: 9527
/* 8473 */    MCD::OPC_Decode, 167, 9, 100, // Opcode: XVABSDP
/* 8477 */    MCD::OPC_FilterValue, 30, 31, 0, // Skip to: 8512
/* 8481 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8484 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8498
/* 8488 */    MCD::OPC_CheckField, 16, 5, 0, 9, 4, // Skip to: 9527
/* 8494 */    MCD::OPC_Decode, 199, 9, 100, // Opcode: XVCVUXDDP
/* 8498 */    MCD::OPC_FilterValue, 1, 1, 4, // Skip to: 9527
/* 8502 */    MCD::OPC_CheckField, 16, 5, 0, 251, 3, // Skip to: 9527
/* 8508 */    MCD::OPC_Decode, 219, 9, 100, // Opcode: XVNABSDP
/* 8512 */    MCD::OPC_FilterValue, 31, 243, 3, // Skip to: 9527
/* 8516 */    MCD::OPC_ExtractField, 2, 2,  // Inst{3-2} ...
/* 8519 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8533
/* 8523 */    MCD::OPC_CheckField, 16, 5, 0, 230, 3, // Skip to: 9527
/* 8529 */    MCD::OPC_Decode, 195, 9, 100, // Opcode: XVCVSXDDP
/* 8533 */    MCD::OPC_FilterValue, 1, 222, 3, // Skip to: 9527
/* 8537 */    MCD::OPC_CheckField, 16, 5, 0, 216, 3, // Skip to: 9527
/* 8543 */    MCD::OPC_Decode, 221, 9, 100, // Opcode: XVNEGDP
/* 8547 */    MCD::OPC_FilterValue, 3, 208, 3, // Skip to: 9527
/* 8551 */    MCD::OPC_Decode, 134, 10, 103, // Opcode: XXSEL
/* 8555 */    MCD::OPC_FilterValue, 62, 19, 0, // Skip to: 8578
/* 8559 */    MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 8562 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 8570
/* 8566 */    MCD::OPC_Decode, 230, 6, 85, // Opcode: STD
/* 8570 */    MCD::OPC_FilterValue, 1, 185, 3, // Skip to: 9527
/* 8574 */    MCD::OPC_Decode, 234, 6, 85, // Opcode: STDU
/* 8578 */    MCD::OPC_FilterValue, 63, 177, 3, // Skip to: 9527
/* 8582 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 8585 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 8605
/* 8589 */    MCD::OPC_CheckField, 21, 2, 0, 164, 3, // Skip to: 9527
/* 8595 */    MCD::OPC_CheckField, 6, 5, 0, 158, 3, // Skip to: 9527
/* 8601 */    MCD::OPC_Decode, 234, 3, 104, // Opcode: FCMPUS
/* 8605 */    MCD::OPC_FilterValue, 12, 19, 0, // Skip to: 8628
/* 8609 */    MCD::OPC_ExtractField, 6, 15,  // Inst{20-6} ...
/* 8612 */    MCD::OPC_FilterValue, 1, 4, 0, // Skip to: 8620
/* 8616 */    MCD::OPC_Decode, 199, 5, 75, // Opcode: MTFSB1
/* 8620 */    MCD::OPC_FilterValue, 2, 135, 3, // Skip to: 9527
/* 8624 */    MCD::OPC_Decode, 198, 5, 75, // Opcode: MTFSB0
/* 8628 */    MCD::OPC_FilterValue, 14, 37, 0, // Skip to: 8669
/* 8632 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 8635 */    MCD::OPC_FilterValue, 18, 10, 0, // Skip to: 8649
/* 8639 */    MCD::OPC_CheckField, 11, 10, 0, 114, 3, // Skip to: 9527
/* 8645 */    MCD::OPC_Decode, 176, 5, 105, // Opcode: MFFS
/* 8649 */    MCD::OPC_FilterValue, 22, 106, 3, // Skip to: 9527
/* 8653 */    MCD::OPC_CheckField, 25, 1, 0, 100, 3, // Skip to: 9527
/* 8659 */    MCD::OPC_CheckField, 16, 1, 0, 94, 3, // Skip to: 9527
/* 8665 */    MCD::OPC_Decode, 200, 5, 106, // Opcode: MTFSF
/* 8669 */    MCD::OPC_FilterValue, 16, 123, 0, // Skip to: 8796
/* 8673 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 8676 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 8684
/* 8680 */    MCD::OPC_Decode, 237, 3, 87, // Opcode: FCPSGNS
/* 8684 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 8698
/* 8688 */    MCD::OPC_CheckField, 16, 5, 0, 65, 3, // Skip to: 9527
/* 8694 */    MCD::OPC_Decode, 147, 4, 88, // Opcode: FNEGS
/* 8698 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 8712
/* 8702 */    MCD::OPC_CheckField, 16, 5, 0, 51, 3, // Skip to: 9527
/* 8708 */    MCD::OPC_Decode, 131, 4, 88, // Opcode: FMR
/* 8712 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 8726
/* 8716 */    MCD::OPC_CheckField, 16, 5, 0, 37, 3, // Skip to: 9527
/* 8722 */    MCD::OPC_Decode, 143, 4, 88, // Opcode: FNABSS
/* 8726 */    MCD::OPC_FilterValue, 8, 10, 0, // Skip to: 8740
/* 8730 */    MCD::OPC_CheckField, 16, 5, 0, 23, 3, // Skip to: 9527
/* 8736 */    MCD::OPC_Decode, 218, 3, 88, // Opcode: FABSS
/* 8740 */    MCD::OPC_FilterValue, 12, 10, 0, // Skip to: 8754
/* 8744 */    MCD::OPC_CheckField, 16, 5, 0, 9, 3, // Skip to: 9527
/* 8750 */    MCD::OPC_Decode, 167, 4, 88, // Opcode: FRINS
/* 8754 */    MCD::OPC_FilterValue, 13, 10, 0, // Skip to: 8768
/* 8758 */    MCD::OPC_CheckField, 16, 5, 0, 251, 2, // Skip to: 9527
/* 8764 */    MCD::OPC_Decode, 175, 4, 88, // Opcode: FRIZS
/* 8768 */    MCD::OPC_FilterValue, 14, 10, 0, // Skip to: 8782
/* 8772 */    MCD::OPC_CheckField, 16, 5, 0, 237, 2, // Skip to: 9527
/* 8778 */    MCD::OPC_Decode, 171, 4, 88, // Opcode: FRIPS
/* 8782 */    MCD::OPC_FilterValue, 15, 229, 2, // Skip to: 9527
/* 8786 */    MCD::OPC_CheckField, 16, 5, 0, 223, 2, // Skip to: 9527
/* 8792 */    MCD::OPC_Decode, 163, 4, 88, // Opcode: FRIMS
/* 8796 */    MCD::OPC_FilterValue, 17, 123, 0, // Skip to: 8923
/* 8800 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 8803 */    MCD::OPC_FilterValue, 0, 4, 0, // Skip to: 8811
/* 8807 */    MCD::OPC_Decode, 238, 3, 87, // Opcode: FCPSGNSo
/* 8811 */    MCD::OPC_FilterValue, 1, 10, 0, // Skip to: 8825
/* 8815 */    MCD::OPC_CheckField, 16, 5, 0, 194, 2, // Skip to: 9527
/* 8821 */    MCD::OPC_Decode, 148, 4, 88, // Opcode: FNEGSo
/* 8825 */    MCD::OPC_FilterValue, 2, 10, 0, // Skip to: 8839
/* 8829 */    MCD::OPC_CheckField, 16, 5, 0, 180, 2, // Skip to: 9527
/* 8835 */    MCD::OPC_Decode, 132, 4, 88, // Opcode: FMRo
/* 8839 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 8853
/* 8843 */    MCD::OPC_CheckField, 16, 5, 0, 166, 2, // Skip to: 9527
/* 8849 */    MCD::OPC_Decode, 144, 4, 88, // Opcode: FNABSSo
/* 8853 */    MCD::OPC_FilterValue, 8, 10, 0, // Skip to: 8867
/* 8857 */    MCD::OPC_CheckField, 16, 5, 0, 152, 2, // Skip to: 9527
/* 8863 */    MCD::OPC_Decode, 219, 3, 88, // Opcode: FABSSo
/* 8867 */    MCD::OPC_FilterValue, 12, 10, 0, // Skip to: 8881
/* 8871 */    MCD::OPC_CheckField, 16, 5, 0, 138, 2, // Skip to: 9527
/* 8877 */    MCD::OPC_Decode, 168, 4, 88, // Opcode: FRINSo
/* 8881 */    MCD::OPC_FilterValue, 13, 10, 0, // Skip to: 8895
/* 8885 */    MCD::OPC_CheckField, 16, 5, 0, 124, 2, // Skip to: 9527
/* 8891 */    MCD::OPC_Decode, 176, 4, 88, // Opcode: FRIZSo
/* 8895 */    MCD::OPC_FilterValue, 14, 10, 0, // Skip to: 8909
/* 8899 */    MCD::OPC_CheckField, 16, 5, 0, 110, 2, // Skip to: 9527
/* 8905 */    MCD::OPC_Decode, 172, 4, 88, // Opcode: FRIPSo
/* 8909 */    MCD::OPC_FilterValue, 15, 102, 2, // Skip to: 9527
/* 8913 */    MCD::OPC_CheckField, 16, 5, 0, 96, 2, // Skip to: 9527
/* 8919 */    MCD::OPC_Decode, 164, 4, 88, // Opcode: FRIMSo
/* 8923 */    MCD::OPC_FilterValue, 24, 16, 0, // Skip to: 8943
/* 8927 */    MCD::OPC_CheckField, 16, 5, 0, 82, 2, // Skip to: 9527
/* 8933 */    MCD::OPC_CheckField, 6, 5, 0, 76, 2, // Skip to: 9527
/* 8939 */    MCD::OPC_Decode, 177, 4, 86, // Opcode: FRSP
/* 8943 */    MCD::OPC_FilterValue, 25, 16, 0, // Skip to: 8963
/* 8947 */    MCD::OPC_CheckField, 16, 5, 0, 62, 2, // Skip to: 9527
/* 8953 */    MCD::OPC_CheckField, 6, 5, 0, 56, 2, // Skip to: 9527
/* 8959 */    MCD::OPC_Decode, 178, 4, 86, // Opcode: FRSPo
/* 8963 */    MCD::OPC_FilterValue, 28, 59, 0, // Skip to: 9026
/* 8967 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 8970 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 8984
/* 8974 */    MCD::OPC_CheckField, 16, 5, 0, 35, 2, // Skip to: 9527
/* 8980 */    MCD::OPC_Decode, 245, 3, 107, // Opcode: FCTIW
/* 8984 */    MCD::OPC_FilterValue, 25, 10, 0, // Skip to: 8998
/* 8988 */    MCD::OPC_CheckField, 16, 5, 0, 21, 2, // Skip to: 9527
/* 8994 */    MCD::OPC_Decode, 239, 3, 107, // Opcode: FCTID
/* 8998 */    MCD::OPC_FilterValue, 26, 10, 0, // Skip to: 9012
/* 9002 */    MCD::OPC_CheckField, 16, 5, 0, 7, 2, // Skip to: 9527
/* 9008 */    MCD::OPC_Decode, 225, 3, 107, // Opcode: FCFID
/* 9012 */    MCD::OPC_FilterValue, 30, 255, 1, // Skip to: 9527
/* 9016 */    MCD::OPC_CheckField, 16, 5, 0, 249, 1, // Skip to: 9527
/* 9022 */    MCD::OPC_Decode, 228, 3, 107, // Opcode: FCFIDU
/* 9026 */    MCD::OPC_FilterValue, 29, 59, 0, // Skip to: 9089
/* 9030 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 9033 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 9047
/* 9037 */    MCD::OPC_CheckField, 16, 5, 0, 228, 1, // Skip to: 9527
/* 9043 */    MCD::OPC_Decode, 250, 3, 107, // Opcode: FCTIWo
/* 9047 */    MCD::OPC_FilterValue, 25, 10, 0, // Skip to: 9061
/* 9051 */    MCD::OPC_CheckField, 16, 5, 0, 214, 1, // Skip to: 9527
/* 9057 */    MCD::OPC_Decode, 244, 3, 107, // Opcode: FCTIDo
/* 9061 */    MCD::OPC_FilterValue, 26, 10, 0, // Skip to: 9075
/* 9065 */    MCD::OPC_CheckField, 16, 5, 0, 200, 1, // Skip to: 9527
/* 9071 */    MCD::OPC_Decode, 232, 3, 107, // Opcode: FCFIDo
/* 9075 */    MCD::OPC_FilterValue, 30, 192, 1, // Skip to: 9527
/* 9079 */    MCD::OPC_CheckField, 16, 5, 0, 186, 1, // Skip to: 9527
/* 9085 */    MCD::OPC_Decode, 231, 3, 107, // Opcode: FCFIDUo
/* 9089 */    MCD::OPC_FilterValue, 30, 59, 0, // Skip to: 9152
/* 9093 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 9096 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 9110
/* 9100 */    MCD::OPC_CheckField, 16, 5, 0, 165, 1, // Skip to: 9527
/* 9106 */    MCD::OPC_Decode, 248, 3, 107, // Opcode: FCTIWZ
/* 9110 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 9124
/* 9114 */    MCD::OPC_CheckField, 16, 5, 0, 151, 1, // Skip to: 9527
/* 9120 */    MCD::OPC_Decode, 246, 3, 107, // Opcode: FCTIWUZ
/* 9124 */    MCD::OPC_FilterValue, 25, 10, 0, // Skip to: 9138
/* 9128 */    MCD::OPC_CheckField, 16, 5, 0, 137, 1, // Skip to: 9527
/* 9134 */    MCD::OPC_Decode, 242, 3, 107, // Opcode: FCTIDZ
/* 9138 */    MCD::OPC_FilterValue, 29, 129, 1, // Skip to: 9527
/* 9142 */    MCD::OPC_CheckField, 16, 5, 0, 123, 1, // Skip to: 9527
/* 9148 */    MCD::OPC_Decode, 240, 3, 107, // Opcode: FCTIDUZ
/* 9152 */    MCD::OPC_FilterValue, 31, 59, 0, // Skip to: 9215
/* 9156 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 9159 */    MCD::OPC_FilterValue, 0, 10, 0, // Skip to: 9173
/* 9163 */    MCD::OPC_CheckField, 16, 5, 0, 102, 1, // Skip to: 9527
/* 9169 */    MCD::OPC_Decode, 249, 3, 107, // Opcode: FCTIWZo
/* 9173 */    MCD::OPC_FilterValue, 4, 10, 0, // Skip to: 9187
/* 9177 */    MCD::OPC_CheckField, 16, 5, 0, 88, 1, // Skip to: 9527
/* 9183 */    MCD::OPC_Decode, 247, 3, 107, // Opcode: FCTIWUZo
/* 9187 */    MCD::OPC_FilterValue, 25, 10, 0, // Skip to: 9201
/* 9191 */    MCD::OPC_CheckField, 16, 5, 0, 74, 1, // Skip to: 9527
/* 9197 */    MCD::OPC_Decode, 243, 3, 107, // Opcode: FCTIDZo
/* 9201 */    MCD::OPC_FilterValue, 29, 66, 1, // Skip to: 9527
/* 9205 */    MCD::OPC_CheckField, 16, 5, 0, 60, 1, // Skip to: 9527
/* 9211 */    MCD::OPC_Decode, 241, 3, 107, // Opcode: FCTIDUZo
/* 9215 */    MCD::OPC_FilterValue, 36, 10, 0, // Skip to: 9229
/* 9219 */    MCD::OPC_CheckField, 6, 5, 0, 46, 1, // Skip to: 9527
/* 9225 */    MCD::OPC_Decode, 251, 3, 108, // Opcode: FDIV
/* 9229 */    MCD::OPC_FilterValue, 37, 10, 0, // Skip to: 9243
/* 9233 */    MCD::OPC_CheckField, 6, 5, 0, 32, 1, // Skip to: 9527
/* 9239 */    MCD::OPC_Decode, 254, 3, 108, // Opcode: FDIVo
/* 9243 */    MCD::OPC_FilterValue, 40, 10, 0, // Skip to: 9257
/* 9247 */    MCD::OPC_CheckField, 6, 5, 0, 18, 1, // Skip to: 9527
/* 9253 */    MCD::OPC_Decode, 191, 4, 108, // Opcode: FSUB
/* 9257 */    MCD::OPC_FilterValue, 41, 10, 0, // Skip to: 9271
/* 9261 */    MCD::OPC_CheckField, 6, 5, 0, 4, 1, // Skip to: 9527
/* 9267 */    MCD::OPC_Decode, 194, 4, 108, // Opcode: FSUBo
/* 9271 */    MCD::OPC_FilterValue, 42, 10, 0, // Skip to: 9285
/* 9275 */    MCD::OPC_CheckField, 6, 5, 0, 246, 0, // Skip to: 9527
/* 9281 */    MCD::OPC_Decode, 220, 3, 108, // Opcode: FADD
/* 9285 */    MCD::OPC_FilterValue, 43, 10, 0, // Skip to: 9299
/* 9289 */    MCD::OPC_CheckField, 6, 5, 0, 232, 0, // Skip to: 9527
/* 9295 */    MCD::OPC_Decode, 223, 3, 108, // Opcode: FADDo
/* 9299 */    MCD::OPC_FilterValue, 44, 16, 0, // Skip to: 9319
/* 9303 */    MCD::OPC_CheckField, 16, 5, 0, 218, 0, // Skip to: 9527
/* 9309 */    MCD::OPC_CheckField, 6, 5, 0, 212, 0, // Skip to: 9527
/* 9315 */    MCD::OPC_Decode, 187, 4, 107, // Opcode: FSQRT
/* 9319 */    MCD::OPC_FilterValue, 45, 16, 0, // Skip to: 9339
/* 9323 */    MCD::OPC_CheckField, 16, 5, 0, 198, 0, // Skip to: 9527
/* 9329 */    MCD::OPC_CheckField, 6, 5, 0, 192, 0, // Skip to: 9527
/* 9335 */    MCD::OPC_Decode, 190, 4, 107, // Opcode: FSQRTo
/* 9339 */    MCD::OPC_FilterValue, 46, 4, 0, // Skip to: 9347
/* 9343 */    MCD::OPC_Decode, 185, 4, 109, // Opcode: FSELS
/* 9347 */    MCD::OPC_FilterValue, 47, 4, 0, // Skip to: 9355
/* 9351 */    MCD::OPC_Decode, 186, 4, 109, // Opcode: FSELSo
/* 9355 */    MCD::OPC_FilterValue, 48, 16, 0, // Skip to: 9375
/* 9359 */    MCD::OPC_CheckField, 16, 5, 0, 162, 0, // Skip to: 9527
/* 9365 */    MCD::OPC_CheckField, 6, 5, 0, 156, 0, // Skip to: 9527
/* 9371 */    MCD::OPC_Decode, 157, 4, 107, // Opcode: FRE
/* 9375 */    MCD::OPC_FilterValue, 49, 16, 0, // Skip to: 9395
/* 9379 */    MCD::OPC_CheckField, 16, 5, 0, 142, 0, // Skip to: 9527
/* 9385 */    MCD::OPC_CheckField, 6, 5, 0, 136, 0, // Skip to: 9527
/* 9391 */    MCD::OPC_Decode, 160, 4, 107, // Opcode: FREo
/* 9395 */    MCD::OPC_FilterValue, 50, 10, 0, // Skip to: 9409
/* 9399 */    MCD::OPC_CheckField, 11, 5, 0, 122, 0, // Skip to: 9527
/* 9405 */    MCD::OPC_Decode, 137, 4, 110, // Opcode: FMUL
/* 9409 */    MCD::OPC_FilterValue, 51, 10, 0, // Skip to: 9423
/* 9413 */    MCD::OPC_CheckField, 11, 5, 0, 108, 0, // Skip to: 9527
/* 9419 */    MCD::OPC_Decode, 140, 4, 110, // Opcode: FMULo
/* 9423 */    MCD::OPC_FilterValue, 52, 16, 0, // Skip to: 9443
/* 9427 */    MCD::OPC_CheckField, 16, 5, 0, 94, 0, // Skip to: 9527
/* 9433 */    MCD::OPC_CheckField, 6, 5, 0, 88, 0, // Skip to: 9527
/* 9439 */    MCD::OPC_Decode, 179, 4, 107, // Opcode: FRSQRTE
/* 9443 */    MCD::OPC_FilterValue, 53, 16, 0, // Skip to: 9463
/* 9447 */    MCD::OPC_CheckField, 16, 5, 0, 74, 0, // Skip to: 9527
/* 9453 */    MCD::OPC_CheckField, 6, 5, 0, 68, 0, // Skip to: 9527
/* 9459 */    MCD::OPC_Decode, 182, 4, 107, // Opcode: FRSQRTEo
/* 9463 */    MCD::OPC_FilterValue, 56, 4, 0, // Skip to: 9471
/* 9467 */    MCD::OPC_Decode, 133, 4, 111, // Opcode: FMSUB
/* 9471 */    MCD::OPC_FilterValue, 57, 4, 0, // Skip to: 9479
/* 9475 */    MCD::OPC_Decode, 136, 4, 111, // Opcode: FMSUBo
/* 9479 */    MCD::OPC_FilterValue, 58, 4, 0, // Skip to: 9487
/* 9483 */    MCD::OPC_Decode, 255, 3, 111, // Opcode: FMADD
/* 9487 */    MCD::OPC_FilterValue, 59, 4, 0, // Skip to: 9495
/* 9491 */    MCD::OPC_Decode, 130, 4, 111, // Opcode: FMADDo
/* 9495 */    MCD::OPC_FilterValue, 60, 4, 0, // Skip to: 9503
/* 9499 */    MCD::OPC_Decode, 153, 4, 111, // Opcode: FNMSUB
/* 9503 */    MCD::OPC_FilterValue, 61, 4, 0, // Skip to: 9511
/* 9507 */    MCD::OPC_Decode, 156, 4, 111, // Opcode: FNMSUBo
/* 9511 */    MCD::OPC_FilterValue, 62, 4, 0, // Skip to: 9519
/* 9515 */    MCD::OPC_Decode, 149, 4, 111, // Opcode: FNMADD
/* 9519 */    MCD::OPC_FilterValue, 63, 4, 0, // Skip to: 9527
/* 9523 */    MCD::OPC_Decode, 152, 4, 111, // Opcode: FNMADDo
/* 9527 */    MCD::OPC_Fail,
  0
};

static bool checkDecoderPredicate(unsigned Idx, uint64_t Bits) {
  llvm_unreachable("Invalid index!");
}

template<typename InsnType>
static DecodeStatus decodeToMCInst(DecodeStatus S, unsigned Idx, InsnType insn, MCInst &MI,
                                   uint64_t Address, const void *Decoder) {
  InsnType tmp;
  switch (Idx) {
  default: llvm_unreachable("Invalid index!");
  case 0:
    return S;
  case 1:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 2:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 3:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 4:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 5:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 6:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 7:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 8:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (decodeSImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 9:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 10:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 4);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 11:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 12:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 13:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeUImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 14:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeUImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 15:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 16:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 17:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 18:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRC_NOR0RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeSImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 19:
    tmp = fieldFromInstruction(insn, 2, 14);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 20:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeCRBITRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 2, 14);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 21:
    tmp = fieldFromInstruction(insn, 5, 7);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 22:
    tmp = fieldFromInstruction(insn, 2, 24);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 23:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 18, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 24:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeCRBITRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 25:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeCRBITRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeCRBITRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeCRBITRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 26:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 27:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 28:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 29:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (decodeUImmOperand<16>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 30:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (decodeUImmOperand<6>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 5, 1) << 5;
    tmp |= fieldFromInstruction(insn, 6, 5) << 0;
    if (decodeUImmOperand<6>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 31:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (decodeUImmOperand<6>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 5, 1) << 5;
    tmp |= fieldFromInstruction(insn, 6, 5) << 0;
    if (decodeUImmOperand<6>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 32:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 5, 1) << 5;
    tmp |= fieldFromInstruction(insn, 6, 5) << 0;
    if (decodeUImmOperand<6>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 33:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 34:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 35:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 36:
    tmp = fieldFromInstruction(insn, 15, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 37:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 11, 5) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 38:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 39:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 40:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeVRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 41:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 42:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 43:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 44:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 45:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 46:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 47:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRC_NOR0RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeCRBITRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 48:
    tmp = fieldFromInstruction(insn, 12, 8);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 49:
    tmp = fieldFromInstruction(insn, 12, 8);
    if (decodeCRBitMOperand(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 50:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 12, 8);
    if (decodeCRBitMOperand(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 51:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 52:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 53:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 54:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 55:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 11, 5) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 56:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 57:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 58:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 59:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 60:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 61:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 62:
    tmp = fieldFromInstruction(insn, 21, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 63:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 64:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 65:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 66:
    tmp = fieldFromInstruction(insn, 21, 2);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 67:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 68:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 69:
    tmp = fieldFromInstruction(insn, 21, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 70:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 71:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 72:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 73:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePointerLikeRegClass1(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodePointerLikeRegClass0(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 74:
    tmp = fieldFromInstruction(insn, 21, 2);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 75:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 76:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 77:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (decodeUImmOperand<5>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 78:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 79:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 80:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 81:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (decodeUImmOperand<6>(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 82:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 21);
    if (decodeMemRIOperands(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 83:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 21);
    if (decodeMemRIOperands(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 84:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 21);
    if (decodeMemRIOperands(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 85:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeG8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 2, 19);
    if (decodeMemRIXOperands(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 86:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 87:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 88:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 89:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 90:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 91:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 92:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 93:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 94:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 95:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 8, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 96:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 97:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 98:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 99:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSFRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 100:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 101:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 102:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 103:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 1) << 5;
    tmp |= fieldFromInstruction(insn, 21, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 2, 1) << 5;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 1, 1) << 5;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 3, 1) << 5;
    tmp |= fieldFromInstruction(insn, 6, 5) << 0;
    if (DecodeVSRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 104:
    tmp = fieldFromInstruction(insn, 23, 3);
    if (DecodeCRRCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 105:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 106:
    tmp = fieldFromInstruction(insn, 17, 8);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 107:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 108:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 109:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF4RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 110:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 111:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeF8RCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  }
}

template<typename InsnType>
static DecodeStatus decodeInstruction(const uint8_t DecodeTable[], MCInst &MI,
                                      InsnType insn, uint64_t Address,
                                      const void *DisAsm,
                                      const MCSubtargetInfo &STI) {
  uint64_t Bits = STI.getFeatureBits();

  const uint8_t *Ptr = DecodeTable;
  uint32_t CurFieldValue = 0;
  DecodeStatus S = MCDisassembler::Success;
  for (;;) {
    ptrdiff_t Loc = Ptr - DecodeTable;
    switch (*Ptr) {
    default:
      errs() << Loc << ": Unexpected decode table opcode!\n";
      return MCDisassembler::Fail;
    case MCD::OPC_ExtractField: {
      unsigned Start = *++Ptr;
      unsigned Len = *++Ptr;
      ++Ptr;
      CurFieldValue = fieldFromInstruction(insn, Start, Len);
      DEBUG(dbgs() << Loc << ": OPC_ExtractField(" << Start << ", "
                   << Len << "): " << CurFieldValue << "\n");
      break;
    }
    case MCD::OPC_FilterValue: {
      // Decode the field value.
      unsigned Len;
      InsnType Val = decodeULEB128(++Ptr, &Len);
      Ptr += Len;
      // NumToSkip is a plain 16-bit integer.
      unsigned NumToSkip = *Ptr++;
      NumToSkip |= (*Ptr++) << 8;

      // Perform the filter operation.
      if (Val != CurFieldValue)
        Ptr += NumToSkip;
      DEBUG(dbgs() << Loc << ": OPC_FilterValue(" << Val << ", " << NumToSkip
                   << "): " << ((Val != CurFieldValue) ? "FAIL:" : "PASS:")
                   << " continuing at " << (Ptr - DecodeTable) << "\n");

      break;
    }
    case MCD::OPC_CheckField: {
      unsigned Start = *++Ptr;
      unsigned Len = *++Ptr;
      InsnType FieldValue = fieldFromInstruction(insn, Start, Len);
      // Decode the field value.
      uint32_t ExpectedValue = decodeULEB128(++Ptr, &Len);
      Ptr += Len;
      // NumToSkip is a plain 16-bit integer.
      unsigned NumToSkip = *Ptr++;
      NumToSkip |= (*Ptr++) << 8;

      // If the actual and expected values don't match, skip.
      if (ExpectedValue != FieldValue)
        Ptr += NumToSkip;
      DEBUG(dbgs() << Loc << ": OPC_CheckField(" << Start << ", "
                   << Len << ", " << ExpectedValue << ", " << NumToSkip
                   << "): FieldValue = " << FieldValue << ", ExpectedValue = "
                   << ExpectedValue << ": "
                   << ((ExpectedValue == FieldValue) ? "PASS\n" : "FAIL\n"));
      break;
    }
    case MCD::OPC_CheckPredicate: {
      unsigned Len;
      // Decode the Predicate Index value.
      unsigned PIdx = decodeULEB128(++Ptr, &Len);
      Ptr += Len;
      // NumToSkip is a plain 16-bit integer.
      unsigned NumToSkip = *Ptr++;
      NumToSkip |= (*Ptr++) << 8;
      // Check the predicate.
      bool Pred;
      if (!(Pred = checkDecoderPredicate(PIdx, Bits)))
        Ptr += NumToSkip;
      (void)Pred;
      DEBUG(dbgs() << Loc << ": OPC_CheckPredicate(" << PIdx << "): "
            << (Pred ? "PASS\n" : "FAIL\n"));

      break;
    }
    case MCD::OPC_Decode: {
      unsigned Len;
      // Decode the Opcode value.
      unsigned Opc = decodeULEB128(++Ptr, &Len);
      Ptr += Len;
      unsigned DecodeIdx = decodeULEB128(Ptr, &Len);
      Ptr += Len;
      DEBUG(dbgs() << Loc << ": OPC_Decode: opcode " << Opc
                   << ", using decoder " << DecodeIdx << "\n" );
      DEBUG(dbgs() << "----- DECODE SUCCESSFUL -----\n");

      MI.setOpcode(Opc);
      return decodeToMCInst(S, DecodeIdx, insn, MI, Address, DisAsm);
    }
    case MCD::OPC_SoftFail: {
      // Decode the mask values.
      unsigned Len;
      InsnType PositiveMask = decodeULEB128(++Ptr, &Len);
      Ptr += Len;
      InsnType NegativeMask = decodeULEB128(Ptr, &Len);
      Ptr += Len;
      bool Fail = (insn & PositiveMask) || (~insn & NegativeMask);
      if (Fail)
        S = MCDisassembler::SoftFail;
      DEBUG(dbgs() << Loc << ": OPC_SoftFail: " << (Fail ? "FAIL\n":"PASS\n"));
      break;
    }
    case MCD::OPC_Fail: {
      DEBUG(dbgs() << Loc << ": OPC_Fail\n");
      return MCDisassembler::Fail;
    }
    }
  }
  llvm_unreachable("bogosity detected in disassembler state machine!");
}


} // End llvm namespace
