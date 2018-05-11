/*===- TableGen'erated file -------------------------------------*- C++ -*-===*\
|*                                                                            *|
|* * Mips Disassembler                                                        *|
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

static const uint8_t DecoderTable16[] = {
/* 0 */       MCD::OPC_ExtractField, 11, 5,  // Inst{15-11} ...
/* 3 */       MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 15
/* 7 */       MCD::OPC_CheckPredicate, 0, 245, 1, // Skip to: 512
/* 11 */      MCD::OPC_Decode, 178, 2, 0, // Opcode: Bimm16
/* 15 */      MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 27
/* 19 */      MCD::OPC_CheckPredicate, 0, 233, 1, // Skip to: 512
/* 23 */      MCD::OPC_Decode, 176, 2, 1, // Opcode: BeqzRxImm16
/* 27 */      MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 39
/* 31 */      MCD::OPC_CheckPredicate, 0, 221, 1, // Skip to: 512
/* 35 */      MCD::OPC_Decode, 180, 2, 1, // Opcode: BnezRxImm16
/* 39 */      MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 51
/* 43 */      MCD::OPC_CheckPredicate, 0, 209, 1, // Skip to: 512
/* 47 */      MCD::OPC_Decode, 156, 1, 2, // Opcode: AddiuRxRxImm16
/* 51 */      MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 63
/* 55 */      MCD::OPC_CheckPredicate, 0, 197, 1, // Skip to: 512
/* 59 */      MCD::OPC_Decode, 138, 13, 1, // Opcode: SltiRxImm16
/* 63 */      MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 75
/* 67 */      MCD::OPC_CheckPredicate, 0, 185, 1, // Skip to: 512
/* 71 */      MCD::OPC_Decode, 141, 13, 1, // Opcode: SltiuRxImm16
/* 75 */      MCD::OPC_FilterValue, 12, 63, 0, // Skip to: 142
/* 79 */      MCD::OPC_ExtractField, 8, 3,  // Inst{10-8} ...
/* 82 */      MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 94
/* 86 */      MCD::OPC_CheckPredicate, 0, 166, 1, // Skip to: 512
/* 90 */      MCD::OPC_Decode, 183, 2, 0, // Opcode: Bteqz16
/* 94 */      MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 106
/* 98 */      MCD::OPC_CheckPredicate, 0, 154, 1, // Skip to: 512
/* 102 */     MCD::OPC_Decode, 191, 2, 0, // Opcode: Btnez16
/* 106 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 118
/* 110 */     MCD::OPC_CheckPredicate, 0, 142, 1, // Skip to: 512
/* 114 */     MCD::OPC_Decode, 159, 1, 0, // Opcode: AddiuSpImm16
/* 118 */     MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 130
/* 122 */     MCD::OPC_CheckPredicate, 0, 130, 1, // Skip to: 512
/* 126 */     MCD::OPC_Decode, 200, 9, 3, // Opcode: Move32R16
/* 130 */     MCD::OPC_FilterValue, 7, 122, 1, // Skip to: 512
/* 134 */     MCD::OPC_CheckPredicate, 0, 118, 1, // Skip to: 512
/* 138 */     MCD::OPC_Decode, 201, 9, 4, // Opcode: MoveR3216
/* 142 */     MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 154
/* 146 */     MCD::OPC_CheckPredicate, 0, 106, 1, // Skip to: 512
/* 150 */     MCD::OPC_Decode, 222, 7, 1, // Opcode: LiRxImm16
/* 154 */     MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 166
/* 158 */     MCD::OPC_CheckPredicate, 0, 94, 1, // Skip to: 512
/* 162 */     MCD::OPC_Decode, 137, 4, 1, // Opcode: CmpiRxImm16
/* 166 */     MCD::OPC_FilterValue, 22, 8, 0, // Skip to: 178
/* 170 */     MCD::OPC_CheckPredicate, 0, 82, 1, // Skip to: 512
/* 174 */     MCD::OPC_Decode, 230, 7, 1, // Opcode: LwRxPcTcp16
/* 178 */     MCD::OPC_FilterValue, 28, 27, 0, // Skip to: 209
/* 182 */     MCD::OPC_ExtractField, 0, 2,  // Inst{1-0} ...
/* 185 */     MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 197
/* 189 */     MCD::OPC_CheckPredicate, 0, 63, 1, // Skip to: 512
/* 193 */     MCD::OPC_Decode, 161, 1, 5, // Opcode: AdduRxRyRz16
/* 197 */     MCD::OPC_FilterValue, 3, 55, 1, // Skip to: 512
/* 201 */     MCD::OPC_CheckPredicate, 0, 51, 1, // Skip to: 512
/* 205 */     MCD::OPC_Decode, 150, 13, 5, // Opcode: SubuRxRyRz16
/* 209 */     MCD::OPC_FilterValue, 29, 43, 1, // Skip to: 512
/* 213 */     MCD::OPC_ExtractField, 0, 5,  // Inst{4-0} ...
/* 216 */     MCD::OPC_FilterValue, 0, 63, 0, // Skip to: 283
/* 220 */     MCD::OPC_ExtractField, 5, 3,  // Inst{7-5} ...
/* 223 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 235
/* 227 */     MCD::OPC_CheckPredicate, 0, 25, 1, // Skip to: 512
/* 231 */     MCD::OPC_Decode, 130, 7, 0, // Opcode: JumpLinkReg16
/* 235 */     MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 253
/* 239 */     MCD::OPC_CheckPredicate, 0, 13, 1, // Skip to: 512
/* 243 */     MCD::OPC_CheckField, 8, 3, 0, 7, 1, // Skip to: 512
/* 249 */     MCD::OPC_Decode, 255, 6, 0, // Opcode: JrRa16
/* 253 */     MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 265
/* 257 */     MCD::OPC_CheckPredicate, 0, 251, 0, // Skip to: 512
/* 261 */     MCD::OPC_Decode, 129, 7, 1, // Opcode: JrcRx16
/* 265 */     MCD::OPC_FilterValue, 7, 243, 0, // Skip to: 512
/* 269 */     MCD::OPC_CheckPredicate, 0, 239, 0, // Skip to: 512
/* 273 */     MCD::OPC_CheckField, 8, 3, 0, 233, 0, // Skip to: 512
/* 279 */     MCD::OPC_Decode, 128, 7, 0, // Opcode: JrcRa16
/* 283 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 295
/* 287 */     MCD::OPC_CheckPredicate, 0, 221, 0, // Skip to: 512
/* 291 */     MCD::OPC_Decode, 136, 13, 6, // Opcode: SltRxRy16
/* 295 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 307
/* 299 */     MCD::OPC_CheckPredicate, 0, 209, 0, // Skip to: 512
/* 303 */     MCD::OPC_Decode, 144, 13, 6, // Opcode: SltuRxRy16
/* 307 */     MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 319
/* 311 */     MCD::OPC_CheckPredicate, 0, 197, 0, // Skip to: 512
/* 315 */     MCD::OPC_Decode, 134, 13, 7, // Opcode: SllvRxRy16
/* 319 */     MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 337
/* 323 */     MCD::OPC_CheckPredicate, 0, 185, 0, // Skip to: 512
/* 327 */     MCD::OPC_CheckField, 5, 6, 0, 179, 0, // Skip to: 512
/* 333 */     MCD::OPC_Decode, 182, 2, 0, // Opcode: Break16
/* 337 */     MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 349
/* 341 */     MCD::OPC_CheckPredicate, 0, 167, 0, // Skip to: 512
/* 345 */     MCD::OPC_Decode, 149, 13, 7, // Opcode: SrlvRxRy16
/* 349 */     MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 361
/* 353 */     MCD::OPC_CheckPredicate, 0, 155, 0, // Skip to: 512
/* 357 */     MCD::OPC_Decode, 147, 13, 7, // Opcode: SravRxRy16
/* 361 */     MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 373
/* 365 */     MCD::OPC_CheckPredicate, 0, 143, 0, // Skip to: 512
/* 369 */     MCD::OPC_Decode, 136, 4, 6, // Opcode: CmpRxRy16
/* 373 */     MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 385
/* 377 */     MCD::OPC_CheckPredicate, 0, 131, 0, // Skip to: 512
/* 381 */     MCD::OPC_Decode, 162, 1, 7, // Opcode: AndRxRxRy16
/* 385 */     MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 397
/* 389 */     MCD::OPC_CheckPredicate, 0, 119, 0, // Skip to: 512
/* 393 */     MCD::OPC_Decode, 248, 9, 7, // Opcode: OrRxRxRy16
/* 397 */     MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 409
/* 401 */     MCD::OPC_CheckPredicate, 0, 107, 0, // Skip to: 512
/* 405 */     MCD::OPC_Decode, 222, 13, 7, // Opcode: XorRxRxRy16
/* 409 */     MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 421
/* 413 */     MCD::OPC_CheckPredicate, 0, 95, 0, // Skip to: 512
/* 417 */     MCD::OPC_Decode, 235, 9, 6, // Opcode: NotRxRy16
/* 421 */     MCD::OPC_FilterValue, 16, 8, 0, // Skip to: 433
/* 425 */     MCD::OPC_CheckPredicate, 0, 83, 0, // Skip to: 512
/* 429 */     MCD::OPC_Decode, 198, 9, 1, // Opcode: Mfhi16
/* 433 */     MCD::OPC_FilterValue, 17, 27, 0, // Skip to: 464
/* 437 */     MCD::OPC_ExtractField, 5, 3,  // Inst{7-5} ...
/* 440 */     MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 452
/* 444 */     MCD::OPC_CheckPredicate, 0, 64, 0, // Skip to: 512
/* 448 */     MCD::OPC_Decode, 244, 12, 2, // Opcode: SebRx16
/* 452 */     MCD::OPC_FilterValue, 5, 56, 0, // Skip to: 512
/* 456 */     MCD::OPC_CheckPredicate, 0, 52, 0, // Skip to: 512
/* 460 */     MCD::OPC_Decode, 245, 12, 2, // Opcode: SehRx16
/* 464 */     MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 476
/* 468 */     MCD::OPC_CheckPredicate, 0, 40, 0, // Skip to: 512
/* 472 */     MCD::OPC_Decode, 199, 9, 1, // Opcode: Mflo16
/* 476 */     MCD::OPC_FilterValue, 26, 8, 0, // Skip to: 488
/* 480 */     MCD::OPC_CheckPredicate, 0, 28, 0, // Skip to: 512
/* 484 */     MCD::OPC_Decode, 246, 4, 6, // Opcode: DivRxRy16
/* 488 */     MCD::OPC_FilterValue, 27, 8, 0, // Skip to: 500
/* 492 */     MCD::OPC_CheckPredicate, 0, 16, 0, // Skip to: 512
/* 496 */     MCD::OPC_Decode, 247, 4, 6, // Opcode: DivuRxRy16
/* 500 */     MCD::OPC_FilterValue, 29, 8, 0, // Skip to: 512
/* 504 */     MCD::OPC_CheckPredicate, 0, 4, 0, // Skip to: 512
/* 508 */     MCD::OPC_Decode, 234, 9, 6, // Opcode: NegRxRy16
/* 512 */     MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTable32[] = {
/* 0 */       MCD::OPC_ExtractField, 11, 5,  // Inst{15-11} ...
/* 3 */       MCD::OPC_FilterValue, 1, 20, 0, // Skip to: 27
/* 7 */       MCD::OPC_CheckPredicate, 0, 198, 1, // Skip to: 465
/* 11 */      MCD::OPC_CheckField, 27, 5, 30, 192, 1, // Skip to: 465
/* 17 */      MCD::OPC_CheckField, 5, 3, 0, 186, 1, // Skip to: 465
/* 23 */      MCD::OPC_Decode, 155, 1, 1, // Opcode: AddiuRxPcImmX16
/* 27 */      MCD::OPC_FilterValue, 2, 20, 0, // Skip to: 51
/* 31 */      MCD::OPC_CheckPredicate, 0, 174, 1, // Skip to: 465
/* 35 */      MCD::OPC_CheckField, 27, 5, 30, 168, 1, // Skip to: 465
/* 41 */      MCD::OPC_CheckField, 5, 6, 0, 162, 1, // Skip to: 465
/* 47 */      MCD::OPC_Decode, 179, 2, 8, // Opcode: BimmX16
/* 51 */      MCD::OPC_FilterValue, 4, 20, 0, // Skip to: 75
/* 55 */      MCD::OPC_CheckPredicate, 0, 150, 1, // Skip to: 465
/* 59 */      MCD::OPC_CheckField, 27, 5, 30, 144, 1, // Skip to: 465
/* 65 */      MCD::OPC_CheckField, 5, 3, 0, 138, 1, // Skip to: 465
/* 71 */      MCD::OPC_Decode, 177, 2, 1, // Opcode: BeqzRxImmX16
/* 75 */      MCD::OPC_FilterValue, 5, 20, 0, // Skip to: 99
/* 79 */      MCD::OPC_CheckPredicate, 0, 126, 1, // Skip to: 465
/* 83 */      MCD::OPC_CheckField, 27, 5, 30, 120, 1, // Skip to: 465
/* 89 */      MCD::OPC_CheckField, 5, 3, 0, 114, 1, // Skip to: 465
/* 95 */      MCD::OPC_Decode, 181, 2, 1, // Opcode: BnezRxImmX16
/* 99 */      MCD::OPC_FilterValue, 6, 92, 0, // Skip to: 195
/* 103 */     MCD::OPC_ExtractField, 27, 5,  // Inst{31-27} ...
/* 106 */     MCD::OPC_FilterValue, 30, 99, 1, // Skip to: 465
/* 110 */     MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 113 */     MCD::OPC_FilterValue, 0, 39, 0, // Skip to: 156
/* 117 */     MCD::OPC_ExtractField, 0, 5,  // Inst{4-0} ...
/* 120 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 132
/* 124 */     MCD::OPC_CheckPredicate, 0, 28, 0, // Skip to: 156
/* 128 */     MCD::OPC_Decode, 133, 13, 6, // Opcode: SllX16
/* 132 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 144
/* 136 */     MCD::OPC_CheckPredicate, 0, 16, 0, // Skip to: 156
/* 140 */     MCD::OPC_Decode, 148, 13, 6, // Opcode: SrlX16
/* 144 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 156
/* 148 */     MCD::OPC_CheckPredicate, 0, 4, 0, // Skip to: 156
/* 152 */     MCD::OPC_Decode, 146, 13, 6, // Opcode: SraX16
/* 156 */     MCD::OPC_ExtractField, 5, 6,  // Inst{10-5} ...
/* 159 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 171
/* 163 */     MCD::OPC_CheckPredicate, 0, 42, 1, // Skip to: 465
/* 167 */     MCD::OPC_Decode, 190, 2, 0, // Opcode: BteqzX16
/* 171 */     MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 183
/* 175 */     MCD::OPC_CheckPredicate, 0, 30, 1, // Skip to: 465
/* 179 */     MCD::OPC_Decode, 198, 2, 0, // Opcode: BtnezX16
/* 183 */     MCD::OPC_FilterValue, 24, 22, 1, // Skip to: 465
/* 187 */     MCD::OPC_CheckPredicate, 0, 18, 1, // Skip to: 465
/* 191 */     MCD::OPC_Decode, 160, 1, 0, // Opcode: AddiuSpImmX16
/* 195 */     MCD::OPC_FilterValue, 8, 20, 0, // Skip to: 219
/* 199 */     MCD::OPC_CheckPredicate, 0, 6, 1, // Skip to: 465
/* 203 */     MCD::OPC_CheckField, 27, 5, 30, 0, 1, // Skip to: 465
/* 209 */     MCD::OPC_CheckField, 4, 1, 0, 250, 0, // Skip to: 465
/* 215 */     MCD::OPC_Decode, 158, 1, 9, // Opcode: AddiuRxRyOffMemX16
/* 219 */     MCD::OPC_FilterValue, 9, 20, 0, // Skip to: 243
/* 223 */     MCD::OPC_CheckPredicate, 0, 238, 0, // Skip to: 465
/* 227 */     MCD::OPC_CheckField, 27, 5, 30, 232, 0, // Skip to: 465
/* 233 */     MCD::OPC_CheckField, 5, 3, 0, 226, 0, // Skip to: 465
/* 239 */     MCD::OPC_Decode, 154, 1, 1, // Opcode: AddiuRxImmX16
/* 243 */     MCD::OPC_FilterValue, 10, 20, 0, // Skip to: 267
/* 247 */     MCD::OPC_CheckPredicate, 0, 214, 0, // Skip to: 465
/* 251 */     MCD::OPC_CheckField, 27, 5, 30, 208, 0, // Skip to: 465
/* 257 */     MCD::OPC_CheckField, 5, 3, 0, 202, 0, // Skip to: 465
/* 263 */     MCD::OPC_Decode, 139, 13, 1, // Opcode: SltiRxImmX16
/* 267 */     MCD::OPC_FilterValue, 11, 20, 0, // Skip to: 291
/* 271 */     MCD::OPC_CheckPredicate, 0, 190, 0, // Skip to: 465
/* 275 */     MCD::OPC_CheckField, 27, 5, 30, 184, 0, // Skip to: 465
/* 281 */     MCD::OPC_CheckField, 5, 3, 0, 178, 0, // Skip to: 465
/* 287 */     MCD::OPC_Decode, 142, 13, 1, // Opcode: SltiuRxImmX16
/* 291 */     MCD::OPC_FilterValue, 13, 20, 0, // Skip to: 315
/* 295 */     MCD::OPC_CheckPredicate, 0, 166, 0, // Skip to: 465
/* 299 */     MCD::OPC_CheckField, 27, 5, 30, 160, 0, // Skip to: 465
/* 305 */     MCD::OPC_CheckField, 5, 3, 0, 154, 0, // Skip to: 465
/* 311 */     MCD::OPC_Decode, 224, 7, 1, // Opcode: LiRxImmX16
/* 315 */     MCD::OPC_FilterValue, 14, 20, 0, // Skip to: 339
/* 319 */     MCD::OPC_CheckPredicate, 0, 142, 0, // Skip to: 465
/* 323 */     MCD::OPC_CheckField, 27, 5, 30, 136, 0, // Skip to: 465
/* 329 */     MCD::OPC_CheckField, 5, 3, 0, 130, 0, // Skip to: 465
/* 335 */     MCD::OPC_Decode, 138, 4, 1, // Opcode: CmpiRxImmX16
/* 339 */     MCD::OPC_FilterValue, 18, 20, 0, // Skip to: 363
/* 343 */     MCD::OPC_CheckPredicate, 0, 118, 0, // Skip to: 465
/* 347 */     MCD::OPC_CheckField, 27, 5, 30, 112, 0, // Skip to: 465
/* 353 */     MCD::OPC_CheckField, 5, 3, 0, 106, 0, // Skip to: 465
/* 359 */     MCD::OPC_Decode, 233, 7, 1, // Opcode: LwRxSpImmX16
/* 363 */     MCD::OPC_FilterValue, 22, 20, 0, // Skip to: 387
/* 367 */     MCD::OPC_CheckPredicate, 0, 94, 0, // Skip to: 465
/* 371 */     MCD::OPC_CheckField, 27, 5, 30, 88, 0, // Skip to: 465
/* 377 */     MCD::OPC_CheckField, 5, 3, 0, 82, 0, // Skip to: 465
/* 383 */     MCD::OPC_Decode, 231, 7, 1, // Opcode: LwRxPcTcpX16
/* 387 */     MCD::OPC_FilterValue, 24, 14, 0, // Skip to: 405
/* 391 */     MCD::OPC_CheckPredicate, 0, 70, 0, // Skip to: 465
/* 395 */     MCD::OPC_CheckField, 27, 5, 30, 64, 0, // Skip to: 465
/* 401 */     MCD::OPC_Decode, 243, 12, 9, // Opcode: SbRxRyOffMemX16
/* 405 */     MCD::OPC_FilterValue, 25, 14, 0, // Skip to: 423
/* 409 */     MCD::OPC_CheckPredicate, 0, 52, 0, // Skip to: 465
/* 413 */     MCD::OPC_CheckField, 27, 5, 30, 46, 0, // Skip to: 465
/* 419 */     MCD::OPC_Decode, 132, 13, 9, // Opcode: ShRxRyOffMemX16
/* 423 */     MCD::OPC_FilterValue, 26, 20, 0, // Skip to: 447
/* 427 */     MCD::OPC_CheckPredicate, 0, 34, 0, // Skip to: 465
/* 431 */     MCD::OPC_CheckField, 27, 5, 30, 28, 0, // Skip to: 465
/* 437 */     MCD::OPC_CheckField, 5, 3, 0, 22, 0, // Skip to: 465
/* 443 */     MCD::OPC_Decode, 152, 13, 1, // Opcode: SwRxSpImmX16
/* 447 */     MCD::OPC_FilterValue, 27, 14, 0, // Skip to: 465
/* 451 */     MCD::OPC_CheckPredicate, 0, 10, 0, // Skip to: 465
/* 455 */     MCD::OPC_CheckField, 27, 5, 30, 4, 0, // Skip to: 465
/* 461 */     MCD::OPC_Decode, 151, 13, 9, // Opcode: SwRxRyOffMemX16
/* 465 */     MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableCOP3_32[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 51, 8, 0, // Skip to: 15
/* 7 */       MCD::OPC_CheckPredicate, 1, 40, 0, // Skip to: 51
/* 11 */      MCD::OPC_Decode, 198, 7, 10, // Opcode: LWC3
/* 15 */      MCD::OPC_FilterValue, 55, 8, 0, // Skip to: 27
/* 19 */      MCD::OPC_CheckPredicate, 2, 28, 0, // Skip to: 51
/* 23 */      MCD::OPC_Decode, 145, 7, 10, // Opcode: LDC3
/* 27 */      MCD::OPC_FilterValue, 59, 8, 0, // Skip to: 39
/* 31 */      MCD::OPC_CheckPredicate, 1, 16, 0, // Skip to: 51
/* 35 */      MCD::OPC_Decode, 217, 12, 10, // Opcode: SWC3
/* 39 */      MCD::OPC_FilterValue, 63, 8, 0, // Skip to: 51
/* 43 */      MCD::OPC_CheckPredicate, 2, 4, 0, // Skip to: 51
/* 47 */      MCD::OPC_Decode, 136, 11, 10, // Opcode: SDC3
/* 51 */      MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMicroMips16[] = {
/* 0 */       MCD::OPC_ExtractField, 10, 6,  // Inst{15-10} ...
/* 3 */       MCD::OPC_FilterValue, 1, 26, 0, // Skip to: 33
/* 7 */       MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 10 */      MCD::OPC_FilterValue, 0, 7, 0, // Skip to: 21
/* 14 */      MCD::OPC_CheckPredicate, 3, 233, 1, // Skip to: 507
/* 18 */      MCD::OPC_Decode, 51, 11, // Opcode: ADDU16_MM
/* 21 */      MCD::OPC_FilterValue, 1, 226, 1, // Skip to: 507
/* 25 */      MCD::OPC_CheckPredicate, 3, 222, 1, // Skip to: 507
/* 29 */      MCD::OPC_Decode, 189, 12, 11, // Opcode: SUBU16_MM
/* 33 */      MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 45
/* 37 */      MCD::OPC_CheckPredicate, 3, 210, 1, // Skip to: 507
/* 41 */      MCD::OPC_Decode, 133, 7, 12, // Opcode: LBU16_MM
/* 45 */      MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 57
/* 49 */      MCD::OPC_CheckPredicate, 3, 198, 1, // Skip to: 507
/* 53 */      MCD::OPC_Decode, 209, 8, 13, // Opcode: MOVE16_MM
/* 57 */      MCD::OPC_FilterValue, 9, 27, 0, // Skip to: 88
/* 61 */      MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 64 */      MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 76
/* 68 */      MCD::OPC_CheckPredicate, 3, 179, 1, // Skip to: 507
/* 72 */      MCD::OPC_Decode, 201, 11, 14, // Opcode: SLL16_MM
/* 76 */      MCD::OPC_FilterValue, 1, 171, 1, // Skip to: 507
/* 80 */      MCD::OPC_CheckPredicate, 3, 167, 1, // Skip to: 507
/* 84 */      MCD::OPC_Decode, 135, 12, 14, // Opcode: SRL16_MM
/* 88 */      MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 100
/* 92 */      MCD::OPC_CheckPredicate, 3, 155, 1, // Skip to: 507
/* 96 */      MCD::OPC_Decode, 164, 7, 12, // Opcode: LHU16_MM
/* 100 */     MCD::OPC_FilterValue, 11, 7, 0, // Skip to: 111
/* 104 */     MCD::OPC_CheckPredicate, 3, 143, 1, // Skip to: 507
/* 108 */     MCD::OPC_Decode, 85, 15, // Opcode: ANDI16_MM
/* 111 */     MCD::OPC_FilterValue, 17, 226, 0, // Skip to: 341
/* 115 */     MCD::OPC_ExtractField, 6, 4,  // Inst{9-6} ...
/* 118 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 130
/* 122 */     MCD::OPC_CheckPredicate, 3, 125, 1, // Skip to: 507
/* 126 */     MCD::OPC_Decode, 233, 9, 16, // Opcode: NOT16_MM
/* 130 */     MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 142
/* 134 */     MCD::OPC_CheckPredicate, 3, 113, 1, // Skip to: 507
/* 138 */     MCD::OPC_Decode, 211, 13, 17, // Opcode: XOR16_MM
/* 142 */     MCD::OPC_FilterValue, 2, 7, 0, // Skip to: 153
/* 146 */     MCD::OPC_CheckPredicate, 3, 101, 1, // Skip to: 507
/* 150 */     MCD::OPC_Decode, 83, 17, // Opcode: AND16_MM
/* 153 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 165
/* 157 */     MCD::OPC_CheckPredicate, 3, 90, 1, // Skip to: 507
/* 161 */     MCD::OPC_Decode, 237, 9, 17, // Opcode: OR16_MM
/* 165 */     MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 177
/* 169 */     MCD::OPC_CheckPredicate, 3, 78, 1, // Skip to: 507
/* 173 */     MCD::OPC_Decode, 202, 7, 18, // Opcode: LWM16_MM
/* 177 */     MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 189
/* 181 */     MCD::OPC_CheckPredicate, 3, 66, 1, // Skip to: 507
/* 185 */     MCD::OPC_Decode, 221, 12, 18, // Opcode: SWM16_MM
/* 189 */     MCD::OPC_FilterValue, 6, 27, 0, // Skip to: 220
/* 193 */     MCD::OPC_ExtractField, 5, 1,  // Inst{5} ...
/* 196 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 208
/* 200 */     MCD::OPC_CheckPredicate, 3, 47, 1, // Skip to: 507
/* 204 */     MCD::OPC_Decode, 245, 6, 19, // Opcode: JR16_MM
/* 208 */     MCD::OPC_FilterValue, 1, 39, 1, // Skip to: 507
/* 212 */     MCD::OPC_CheckPredicate, 3, 35, 1, // Skip to: 507
/* 216 */     MCD::OPC_Decode, 248, 6, 19, // Opcode: JRC16_MM
/* 220 */     MCD::OPC_FilterValue, 7, 27, 0, // Skip to: 251
/* 224 */     MCD::OPC_ExtractField, 5, 1,  // Inst{5} ...
/* 227 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 239
/* 231 */     MCD::OPC_CheckPredicate, 3, 16, 1, // Skip to: 507
/* 235 */     MCD::OPC_Decode, 231, 6, 19, // Opcode: JALR16_MM
/* 239 */     MCD::OPC_FilterValue, 1, 8, 1, // Skip to: 507
/* 243 */     MCD::OPC_CheckPredicate, 3, 4, 1, // Skip to: 507
/* 247 */     MCD::OPC_Decode, 235, 6, 19, // Opcode: JALRS16_MM
/* 251 */     MCD::OPC_FilterValue, 8, 14, 0, // Skip to: 269
/* 255 */     MCD::OPC_CheckPredicate, 3, 248, 0, // Skip to: 507
/* 259 */     MCD::OPC_CheckField, 5, 1, 0, 242, 0, // Skip to: 507
/* 265 */     MCD::OPC_Decode, 163, 8, 19, // Opcode: MFHI16_MM
/* 269 */     MCD::OPC_FilterValue, 9, 14, 0, // Skip to: 287
/* 273 */     MCD::OPC_CheckPredicate, 3, 230, 0, // Skip to: 507
/* 277 */     MCD::OPC_CheckField, 5, 1, 0, 224, 0, // Skip to: 507
/* 283 */     MCD::OPC_Decode, 168, 8, 19, // Opcode: MFLO16_MM
/* 287 */     MCD::OPC_FilterValue, 10, 14, 0, // Skip to: 305
/* 291 */     MCD::OPC_CheckPredicate, 3, 212, 0, // Skip to: 507
/* 295 */     MCD::OPC_CheckField, 4, 2, 0, 206, 0, // Skip to: 507
/* 301 */     MCD::OPC_Decode, 154, 2, 20, // Opcode: BREAK16_MM
/* 305 */     MCD::OPC_FilterValue, 11, 14, 0, // Skip to: 323
/* 309 */     MCD::OPC_CheckPredicate, 3, 194, 0, // Skip to: 507
/* 313 */     MCD::OPC_CheckField, 4, 2, 0, 188, 0, // Skip to: 507
/* 319 */     MCD::OPC_Decode, 128, 11, 20, // Opcode: SDBBP16_MM
/* 323 */     MCD::OPC_FilterValue, 12, 180, 0, // Skip to: 507
/* 327 */     MCD::OPC_CheckPredicate, 3, 176, 0, // Skip to: 507
/* 331 */     MCD::OPC_CheckField, 5, 1, 0, 170, 0, // Skip to: 507
/* 337 */     MCD::OPC_Decode, 247, 6, 21, // Opcode: JRADDIUSP
/* 341 */     MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 353
/* 345 */     MCD::OPC_CheckPredicate, 3, 158, 0, // Skip to: 507
/* 349 */     MCD::OPC_Decode, 209, 7, 22, // Opcode: LWSP_MM
/* 353 */     MCD::OPC_FilterValue, 19, 25, 0, // Skip to: 382
/* 357 */     MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 360 */     MCD::OPC_FilterValue, 0, 7, 0, // Skip to: 371
/* 364 */     MCD::OPC_CheckPredicate, 3, 139, 0, // Skip to: 507
/* 368 */     MCD::OPC_Decode, 29, 23, // Opcode: ADDIUS5_MM
/* 371 */     MCD::OPC_FilterValue, 1, 132, 0, // Skip to: 507
/* 375 */     MCD::OPC_CheckPredicate, 3, 128, 0, // Skip to: 507
/* 379 */     MCD::OPC_Decode, 30, 24, // Opcode: ADDIUSP_MM
/* 382 */     MCD::OPC_FilterValue, 26, 8, 0, // Skip to: 394
/* 386 */     MCD::OPC_CheckPredicate, 3, 117, 0, // Skip to: 507
/* 390 */     MCD::OPC_Decode, 192, 7, 12, // Opcode: LW16_MM
/* 394 */     MCD::OPC_FilterValue, 27, 25, 0, // Skip to: 423
/* 398 */     MCD::OPC_ExtractField, 0, 1,  // Inst{0} ...
/* 401 */     MCD::OPC_FilterValue, 0, 7, 0, // Skip to: 412
/* 405 */     MCD::OPC_CheckPredicate, 3, 98, 0, // Skip to: 507
/* 409 */     MCD::OPC_Decode, 28, 25, // Opcode: ADDIUR2_MM
/* 412 */     MCD::OPC_FilterValue, 1, 91, 0, // Skip to: 507
/* 416 */     MCD::OPC_CheckPredicate, 3, 87, 0, // Skip to: 507
/* 420 */     MCD::OPC_Decode, 27, 26, // Opcode: ADDIUR1SP_MM
/* 423 */     MCD::OPC_FilterValue, 34, 8, 0, // Skip to: 435
/* 427 */     MCD::OPC_CheckPredicate, 3, 76, 0, // Skip to: 507
/* 431 */     MCD::OPC_Decode, 246, 10, 12, // Opcode: SB16_MM
/* 435 */     MCD::OPC_FilterValue, 35, 8, 0, // Skip to: 447
/* 439 */     MCD::OPC_CheckPredicate, 3, 64, 0, // Skip to: 507
/* 443 */     MCD::OPC_Decode, 192, 1, 27, // Opcode: BEQZ16_MM
/* 447 */     MCD::OPC_FilterValue, 42, 8, 0, // Skip to: 459
/* 451 */     MCD::OPC_CheckPredicate, 3, 52, 0, // Skip to: 507
/* 455 */     MCD::OPC_Decode, 162, 11, 12, // Opcode: SH16_MM
/* 459 */     MCD::OPC_FilterValue, 43, 8, 0, // Skip to: 471
/* 463 */     MCD::OPC_CheckPredicate, 3, 40, 0, // Skip to: 507
/* 467 */     MCD::OPC_Decode, 139, 2, 27, // Opcode: BNEZ16_MM
/* 471 */     MCD::OPC_FilterValue, 50, 8, 0, // Skip to: 483
/* 475 */     MCD::OPC_CheckPredicate, 3, 28, 0, // Skip to: 507
/* 479 */     MCD::OPC_Decode, 227, 12, 22, // Opcode: SWSP_MM
/* 483 */     MCD::OPC_FilterValue, 58, 8, 0, // Skip to: 495
/* 487 */     MCD::OPC_CheckPredicate, 3, 16, 0, // Skip to: 507
/* 491 */     MCD::OPC_Decode, 211, 12, 12, // Opcode: SW16_MM
/* 495 */     MCD::OPC_FilterValue, 59, 8, 0, // Skip to: 507
/* 499 */     MCD::OPC_CheckPredicate, 3, 4, 0, // Skip to: 507
/* 503 */     MCD::OPC_Decode, 170, 7, 28, // Opcode: LI16_MM
/* 507 */     MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMicroMips32[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 0, 189, 3, // Skip to: 964
/* 7 */       MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 10 */      MCD::OPC_FilterValue, 0, 90, 0, // Skip to: 104
/* 14 */      MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 17 */      MCD::OPC_FilterValue, 0, 47, 0, // Skip to: 68
/* 21 */      MCD::OPC_ExtractField, 11, 15,  // Inst{25-11} ...
/* 24 */      MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 36
/* 28 */      MCD::OPC_CheckPredicate, 3, 28, 0, // Skip to: 60
/* 32 */      MCD::OPC_Decode, 156, 12, 0, // Opcode: SSNOP_MM
/* 36 */      MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 48
/* 40 */      MCD::OPC_CheckPredicate, 3, 16, 0, // Skip to: 60
/* 44 */      MCD::OPC_Decode, 249, 4, 0, // Opcode: EHB_MM
/* 48 */      MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 60
/* 52 */      MCD::OPC_CheckPredicate, 3, 4, 0, // Skip to: 60
/* 56 */      MCD::OPC_Decode, 251, 9, 0, // Opcode: PAUSE_MM
/* 60 */      MCD::OPC_CheckPredicate, 3, 15, 6, // Skip to: 1615
/* 64 */      MCD::OPC_Decode, 213, 11, 29, // Opcode: SLL_MM
/* 68 */      MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 80
/* 72 */      MCD::OPC_CheckPredicate, 3, 3, 6, // Skip to: 1615
/* 76 */      MCD::OPC_Decode, 153, 12, 29, // Opcode: SRL_MM
/* 80 */      MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 92
/* 84 */      MCD::OPC_CheckPredicate, 3, 247, 5, // Skip to: 1615
/* 88 */      MCD::OPC_Decode, 132, 12, 29, // Opcode: SRA_MM
/* 92 */      MCD::OPC_FilterValue, 3, 239, 5, // Skip to: 1615
/* 96 */      MCD::OPC_CheckPredicate, 3, 235, 5, // Skip to: 1615
/* 100 */     MCD::OPC_Decode, 225, 10, 29, // Opcode: ROTR_MM
/* 104 */     MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 116
/* 108 */     MCD::OPC_CheckPredicate, 3, 223, 5, // Skip to: 1615
/* 112 */     MCD::OPC_Decode, 155, 2, 30, // Opcode: BREAK_MM
/* 116 */     MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 128
/* 120 */     MCD::OPC_CheckPredicate, 3, 211, 5, // Skip to: 1615
/* 124 */     MCD::OPC_Decode, 227, 6, 31, // Opcode: INS_MM
/* 128 */     MCD::OPC_FilterValue, 16, 180, 0, // Skip to: 312
/* 132 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 135 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 147
/* 139 */     MCD::OPC_CheckPredicate, 3, 192, 5, // Skip to: 1615
/* 143 */     MCD::OPC_Decode, 209, 11, 32, // Opcode: SLLV_MM
/* 147 */     MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 159
/* 151 */     MCD::OPC_CheckPredicate, 3, 180, 5, // Skip to: 1615
/* 155 */     MCD::OPC_Decode, 149, 12, 32, // Opcode: SRLV_MM
/* 159 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 171
/* 163 */     MCD::OPC_CheckPredicate, 3, 168, 5, // Skip to: 1615
/* 167 */     MCD::OPC_Decode, 128, 12, 32, // Opcode: SRAV_MM
/* 171 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 183
/* 175 */     MCD::OPC_CheckPredicate, 3, 156, 5, // Skip to: 1615
/* 179 */     MCD::OPC_Decode, 224, 10, 32, // Opcode: ROTRV_MM
/* 183 */     MCD::OPC_FilterValue, 4, 7, 0, // Skip to: 194
/* 187 */     MCD::OPC_CheckPredicate, 3, 144, 5, // Skip to: 1615
/* 191 */     MCD::OPC_Decode, 71, 33, // Opcode: ADD_MM
/* 194 */     MCD::OPC_FilterValue, 5, 7, 0, // Skip to: 205
/* 198 */     MCD::OPC_CheckPredicate, 3, 133, 5, // Skip to: 1615
/* 202 */     MCD::OPC_Decode, 77, 33, // Opcode: ADDu_MM
/* 205 */     MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 217
/* 209 */     MCD::OPC_CheckPredicate, 3, 122, 5, // Skip to: 1615
/* 213 */     MCD::OPC_Decode, 204, 12, 33, // Opcode: SUB_MM
/* 217 */     MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 229
/* 221 */     MCD::OPC_CheckPredicate, 3, 110, 5, // Skip to: 1615
/* 225 */     MCD::OPC_Decode, 206, 12, 33, // Opcode: SUBu_MM
/* 229 */     MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 241
/* 233 */     MCD::OPC_CheckPredicate, 3, 98, 5, // Skip to: 1615
/* 237 */     MCD::OPC_Decode, 192, 9, 33, // Opcode: MUL_MM
/* 241 */     MCD::OPC_FilterValue, 9, 7, 0, // Skip to: 252
/* 245 */     MCD::OPC_CheckPredicate, 3, 86, 5, // Skip to: 1615
/* 249 */     MCD::OPC_Decode, 87, 33, // Opcode: AND_MM
/* 252 */     MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 264
/* 256 */     MCD::OPC_CheckPredicate, 3, 75, 5, // Skip to: 1615
/* 260 */     MCD::OPC_Decode, 240, 9, 33, // Opcode: OR_MM
/* 264 */     MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 276
/* 268 */     MCD::OPC_CheckPredicate, 3, 63, 5, // Skip to: 1615
/* 272 */     MCD::OPC_Decode, 228, 9, 33, // Opcode: NOR_MM
/* 276 */     MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 288
/* 280 */     MCD::OPC_CheckPredicate, 3, 51, 5, // Skip to: 1615
/* 284 */     MCD::OPC_Decode, 214, 13, 33, // Opcode: XOR_MM
/* 288 */     MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 300
/* 292 */     MCD::OPC_CheckPredicate, 3, 39, 5, // Skip to: 1615
/* 296 */     MCD::OPC_Decode, 217, 11, 33, // Opcode: SLT_MM
/* 300 */     MCD::OPC_FilterValue, 14, 31, 5, // Skip to: 1615
/* 304 */     MCD::OPC_CheckPredicate, 3, 27, 5, // Skip to: 1615
/* 308 */     MCD::OPC_Decode, 226, 11, 33, // Opcode: SLTu_MM
/* 312 */     MCD::OPC_FilterValue, 24, 39, 0, // Skip to: 355
/* 316 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 319 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 331
/* 323 */     MCD::OPC_CheckPredicate, 3, 8, 5, // Skip to: 1615
/* 327 */     MCD::OPC_Decode, 228, 8, 34, // Opcode: MOVN_I_MM
/* 331 */     MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 343
/* 335 */     MCD::OPC_CheckPredicate, 3, 252, 4, // Skip to: 1615
/* 339 */     MCD::OPC_Decode, 248, 8, 34, // Opcode: MOVZ_I_MM
/* 343 */     MCD::OPC_FilterValue, 4, 244, 4, // Skip to: 1615
/* 347 */     MCD::OPC_CheckPredicate, 3, 240, 4, // Skip to: 1615
/* 351 */     MCD::OPC_Decode, 215, 7, 35, // Opcode: LWXS_MM
/* 355 */     MCD::OPC_FilterValue, 44, 8, 0, // Skip to: 367
/* 359 */     MCD::OPC_CheckPredicate, 3, 228, 4, // Skip to: 1615
/* 363 */     MCD::OPC_Decode, 141, 5, 36, // Opcode: EXT_MM
/* 367 */     MCD::OPC_FilterValue, 60, 220, 4, // Skip to: 1615
/* 371 */     MCD::OPC_ExtractField, 6, 6,  // Inst{11-6} ...
/* 374 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 386
/* 378 */     MCD::OPC_CheckPredicate, 3, 209, 4, // Skip to: 1615
/* 382 */     MCD::OPC_Decode, 159, 13, 37, // Opcode: TEQ_MM
/* 386 */     MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 398
/* 390 */     MCD::OPC_CheckPredicate, 3, 197, 4, // Skip to: 1615
/* 394 */     MCD::OPC_Decode, 167, 13, 37, // Opcode: TGE_MM
/* 398 */     MCD::OPC_FilterValue, 13, 123, 0, // Skip to: 525
/* 402 */     MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 405 */     MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 423
/* 409 */     MCD::OPC_CheckPredicate, 3, 178, 4, // Skip to: 1615
/* 413 */     MCD::OPC_CheckField, 16, 10, 0, 172, 4, // Skip to: 1615
/* 419 */     MCD::OPC_Decode, 169, 13, 0, // Opcode: TLBP_MM
/* 423 */     MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 441
/* 427 */     MCD::OPC_CheckPredicate, 3, 160, 4, // Skip to: 1615
/* 431 */     MCD::OPC_CheckField, 16, 10, 0, 154, 4, // Skip to: 1615
/* 437 */     MCD::OPC_Decode, 171, 13, 0, // Opcode: TLBR_MM
/* 441 */     MCD::OPC_FilterValue, 2, 14, 0, // Skip to: 459
/* 445 */     MCD::OPC_CheckPredicate, 3, 142, 4, // Skip to: 1615
/* 449 */     MCD::OPC_CheckField, 16, 10, 0, 136, 4, // Skip to: 1615
/* 455 */     MCD::OPC_Decode, 173, 13, 0, // Opcode: TLBWI_MM
/* 459 */     MCD::OPC_FilterValue, 3, 14, 0, // Skip to: 477
/* 463 */     MCD::OPC_CheckPredicate, 3, 124, 4, // Skip to: 1615
/* 467 */     MCD::OPC_CheckField, 16, 10, 0, 118, 4, // Skip to: 1615
/* 473 */     MCD::OPC_Decode, 175, 13, 0, // Opcode: TLBWR_MM
/* 477 */     MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 489
/* 481 */     MCD::OPC_CheckPredicate, 3, 106, 4, // Skip to: 1615
/* 485 */     MCD::OPC_Decode, 206, 13, 38, // Opcode: WAIT_MM
/* 489 */     MCD::OPC_FilterValue, 14, 14, 0, // Skip to: 507
/* 493 */     MCD::OPC_CheckPredicate, 3, 94, 4, // Skip to: 1615
/* 497 */     MCD::OPC_CheckField, 16, 10, 0, 88, 4, // Skip to: 1615
/* 503 */     MCD::OPC_Decode, 156, 4, 0, // Opcode: DERET_MM
/* 507 */     MCD::OPC_FilterValue, 15, 80, 4, // Skip to: 1615
/* 511 */     MCD::OPC_CheckPredicate, 3, 76, 4, // Skip to: 1615
/* 515 */     MCD::OPC_CheckField, 16, 10, 0, 70, 4, // Skip to: 1615
/* 521 */     MCD::OPC_Decode, 253, 4, 0, // Opcode: ERET_MM
/* 525 */     MCD::OPC_FilterValue, 16, 8, 0, // Skip to: 537
/* 529 */     MCD::OPC_CheckPredicate, 3, 58, 4, // Skip to: 1615
/* 533 */     MCD::OPC_Decode, 166, 13, 37, // Opcode: TGEU_MM
/* 537 */     MCD::OPC_FilterValue, 29, 39, 0, // Skip to: 580
/* 541 */     MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 544 */     MCD::OPC_FilterValue, 4, 14, 0, // Skip to: 562
/* 548 */     MCD::OPC_CheckPredicate, 3, 39, 4, // Skip to: 1615
/* 552 */     MCD::OPC_CheckField, 21, 5, 0, 33, 4, // Skip to: 1615
/* 558 */     MCD::OPC_Decode, 174, 4, 39, // Opcode: DI_MM
/* 562 */     MCD::OPC_FilterValue, 5, 25, 4, // Skip to: 1615
/* 566 */     MCD::OPC_CheckPredicate, 3, 21, 4, // Skip to: 1615
/* 570 */     MCD::OPC_CheckField, 21, 5, 0, 15, 4, // Skip to: 1615
/* 576 */     MCD::OPC_Decode, 251, 4, 39, // Opcode: EI_MM
/* 580 */     MCD::OPC_FilterValue, 32, 8, 0, // Skip to: 592
/* 584 */     MCD::OPC_CheckPredicate, 3, 3, 4, // Skip to: 1615
/* 588 */     MCD::OPC_Decode, 182, 13, 37, // Opcode: TLT_MM
/* 592 */     MCD::OPC_FilterValue, 40, 8, 0, // Skip to: 604
/* 596 */     MCD::OPC_CheckPredicate, 3, 247, 3, // Skip to: 1615
/* 600 */     MCD::OPC_Decode, 181, 13, 37, // Opcode: TLTU_MM
/* 604 */     MCD::OPC_FilterValue, 44, 171, 0, // Skip to: 779
/* 608 */     MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 611 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 623
/* 615 */     MCD::OPC_CheckPredicate, 3, 228, 3, // Skip to: 1615
/* 619 */     MCD::OPC_Decode, 145, 11, 40, // Opcode: SEB_MM
/* 623 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 635
/* 627 */     MCD::OPC_CheckPredicate, 3, 216, 3, // Skip to: 1615
/* 631 */     MCD::OPC_Decode, 148, 11, 40, // Opcode: SEH_MM
/* 635 */     MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 647
/* 639 */     MCD::OPC_CheckPredicate, 3, 204, 3, // Skip to: 1615
/* 643 */     MCD::OPC_Decode, 243, 2, 40, // Opcode: CLO_MM
/* 647 */     MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 659
/* 651 */     MCD::OPC_CheckPredicate, 3, 192, 3, // Skip to: 1615
/* 655 */     MCD::OPC_Decode, 134, 3, 40, // Opcode: CLZ_MM
/* 659 */     MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 671
/* 663 */     MCD::OPC_CheckPredicate, 3, 180, 3, // Skip to: 1615
/* 667 */     MCD::OPC_Decode, 215, 10, 41, // Opcode: RDHWR_MM
/* 671 */     MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 683
/* 675 */     MCD::OPC_CheckPredicate, 3, 168, 3, // Skip to: 1615
/* 679 */     MCD::OPC_Decode, 209, 13, 40, // Opcode: WSBH_MM
/* 683 */     MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 695
/* 687 */     MCD::OPC_CheckPredicate, 3, 156, 3, // Skip to: 1615
/* 691 */     MCD::OPC_Decode, 184, 9, 42, // Opcode: MULT_MM
/* 695 */     MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 707
/* 699 */     MCD::OPC_CheckPredicate, 3, 144, 3, // Skip to: 1615
/* 703 */     MCD::OPC_Decode, 186, 9, 42, // Opcode: MULTu_MM
/* 707 */     MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 719
/* 711 */     MCD::OPC_CheckPredicate, 3, 132, 3, // Skip to: 1615
/* 715 */     MCD::OPC_Decode, 138, 11, 42, // Opcode: SDIV_MM
/* 719 */     MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 731
/* 723 */     MCD::OPC_CheckPredicate, 3, 120, 3, // Skip to: 1615
/* 727 */     MCD::OPC_Decode, 197, 13, 42, // Opcode: UDIV_MM
/* 731 */     MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 743
/* 735 */     MCD::OPC_CheckPredicate, 3, 108, 3, // Skip to: 1615
/* 739 */     MCD::OPC_Decode, 250, 7, 42, // Opcode: MADD_MM
/* 743 */     MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 755
/* 747 */     MCD::OPC_CheckPredicate, 3, 96, 3, // Skip to: 1615
/* 751 */     MCD::OPC_Decode, 241, 7, 42, // Opcode: MADDU_MM
/* 755 */     MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 767
/* 759 */     MCD::OPC_CheckPredicate, 3, 84, 3, // Skip to: 1615
/* 763 */     MCD::OPC_Decode, 139, 9, 42, // Opcode: MSUB_MM
/* 767 */     MCD::OPC_FilterValue, 15, 76, 3, // Skip to: 1615
/* 771 */     MCD::OPC_CheckPredicate, 3, 72, 3, // Skip to: 1615
/* 775 */     MCD::OPC_Decode, 130, 9, 42, // Opcode: MSUBU_MM
/* 779 */     MCD::OPC_FilterValue, 45, 45, 0, // Skip to: 828
/* 783 */     MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 786 */     MCD::OPC_FilterValue, 6, 14, 0, // Skip to: 804
/* 790 */     MCD::OPC_CheckPredicate, 3, 53, 3, // Skip to: 1615
/* 794 */     MCD::OPC_CheckField, 21, 5, 0, 47, 3, // Skip to: 1615
/* 800 */     MCD::OPC_Decode, 233, 12, 43, // Opcode: SYNC_MM
/* 804 */     MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 816
/* 808 */     MCD::OPC_CheckPredicate, 3, 35, 3, // Skip to: 1615
/* 812 */     MCD::OPC_Decode, 235, 12, 38, // Opcode: SYSCALL_MM
/* 816 */     MCD::OPC_FilterValue, 13, 27, 3, // Skip to: 1615
/* 820 */     MCD::OPC_CheckPredicate, 3, 23, 3, // Skip to: 1615
/* 824 */     MCD::OPC_Decode, 129, 11, 38, // Opcode: SDBBP_MM
/* 828 */     MCD::OPC_FilterValue, 48, 8, 0, // Skip to: 840
/* 832 */     MCD::OPC_CheckPredicate, 3, 11, 3, // Skip to: 1615
/* 836 */     MCD::OPC_Decode, 186, 13, 37, // Opcode: TNE_MM
/* 840 */     MCD::OPC_FilterValue, 53, 75, 0, // Skip to: 919
/* 844 */     MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 847 */     MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 865
/* 851 */     MCD::OPC_CheckPredicate, 3, 248, 2, // Skip to: 1615
/* 855 */     MCD::OPC_CheckField, 21, 5, 0, 242, 2, // Skip to: 1615
/* 861 */     MCD::OPC_Decode, 166, 8, 39, // Opcode: MFHI_MM
/* 865 */     MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 883
/* 869 */     MCD::OPC_CheckPredicate, 3, 230, 2, // Skip to: 1615
/* 873 */     MCD::OPC_CheckField, 21, 5, 0, 224, 2, // Skip to: 1615
/* 879 */     MCD::OPC_Decode, 171, 8, 39, // Opcode: MFLO_MM
/* 883 */     MCD::OPC_FilterValue, 2, 14, 0, // Skip to: 901
/* 887 */     MCD::OPC_CheckPredicate, 3, 212, 2, // Skip to: 1615
/* 891 */     MCD::OPC_CheckField, 21, 5, 0, 206, 2, // Skip to: 1615
/* 897 */     MCD::OPC_Decode, 154, 9, 39, // Opcode: MTHI_MM
/* 901 */     MCD::OPC_FilterValue, 3, 198, 2, // Skip to: 1615
/* 905 */     MCD::OPC_CheckPredicate, 3, 194, 2, // Skip to: 1615
/* 909 */     MCD::OPC_CheckField, 21, 5, 0, 188, 2, // Skip to: 1615
/* 915 */     MCD::OPC_Decode, 159, 9, 39, // Opcode: MTLO_MM
/* 919 */     MCD::OPC_FilterValue, 60, 180, 2, // Skip to: 1615
/* 923 */     MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 926 */     MCD::OPC_FilterValue, 0, 22, 0, // Skip to: 952
/* 930 */     MCD::OPC_CheckPredicate, 3, 10, 0, // Skip to: 944
/* 934 */     MCD::OPC_CheckField, 21, 5, 0, 4, 0, // Skip to: 944
/* 940 */     MCD::OPC_Decode, 251, 6, 39, // Opcode: JR_MM
/* 944 */     MCD::OPC_CheckPredicate, 3, 155, 2, // Skip to: 1615
/* 948 */     MCD::OPC_Decode, 238, 6, 40, // Opcode: JALR_MM
/* 952 */     MCD::OPC_FilterValue, 4, 147, 2, // Skip to: 1615
/* 956 */     MCD::OPC_CheckPredicate, 3, 143, 2, // Skip to: 1615
/* 960 */     MCD::OPC_Decode, 236, 6, 40, // Opcode: JALRS_MM
/* 964 */     MCD::OPC_FilterValue, 4, 7, 0, // Skip to: 975
/* 968 */     MCD::OPC_CheckPredicate, 3, 131, 2, // Skip to: 1615
/* 972 */     MCD::OPC_Decode, 73, 44, // Opcode: ADDi_MM
/* 975 */     MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 987
/* 979 */     MCD::OPC_CheckPredicate, 3, 120, 2, // Skip to: 1615
/* 983 */     MCD::OPC_Decode, 138, 7, 45, // Opcode: LBu_MM
/* 987 */     MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 999
/* 991 */     MCD::OPC_CheckPredicate, 3, 108, 2, // Skip to: 1615
/* 995 */     MCD::OPC_Decode, 248, 10, 45, // Opcode: SB_MM
/* 999 */     MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 1011
/* 1003 */    MCD::OPC_CheckPredicate, 3, 96, 2, // Skip to: 1615
/* 1007 */    MCD::OPC_Decode, 135, 7, 45, // Opcode: LB_MM
/* 1011 */    MCD::OPC_FilterValue, 8, 63, 0, // Skip to: 1078
/* 1015 */    MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 1018 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 1030
/* 1022 */    MCD::OPC_CheckPredicate, 3, 77, 2, // Skip to: 1615
/* 1026 */    MCD::OPC_Decode, 205, 7, 46, // Opcode: LWP_MM
/* 1030 */    MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 1042
/* 1034 */    MCD::OPC_CheckPredicate, 3, 65, 2, // Skip to: 1615
/* 1038 */    MCD::OPC_Decode, 203, 7, 46, // Opcode: LWM32_MM
/* 1042 */    MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 1054
/* 1046 */    MCD::OPC_CheckPredicate, 3, 53, 2, // Skip to: 1615
/* 1050 */    MCD::OPC_Decode, 202, 2, 47, // Opcode: CACHE_MM
/* 1054 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 1066
/* 1058 */    MCD::OPC_CheckPredicate, 3, 41, 2, // Skip to: 1615
/* 1062 */    MCD::OPC_Decode, 223, 12, 46, // Opcode: SWP_MM
/* 1066 */    MCD::OPC_FilterValue, 13, 33, 2, // Skip to: 1615
/* 1070 */    MCD::OPC_CheckPredicate, 3, 29, 2, // Skip to: 1615
/* 1074 */    MCD::OPC_Decode, 222, 12, 46, // Opcode: SWM32_MM
/* 1078 */    MCD::OPC_FilterValue, 12, 7, 0, // Skip to: 1089
/* 1082 */    MCD::OPC_CheckPredicate, 3, 17, 2, // Skip to: 1615
/* 1086 */    MCD::OPC_Decode, 75, 44, // Opcode: ADDiu_MM
/* 1089 */    MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 1101
/* 1093 */    MCD::OPC_CheckPredicate, 3, 6, 2, // Skip to: 1615
/* 1097 */    MCD::OPC_Decode, 169, 7, 45, // Opcode: LHu_MM
/* 1101 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 1113
/* 1105 */    MCD::OPC_CheckPredicate, 3, 250, 1, // Skip to: 1615
/* 1109 */    MCD::OPC_Decode, 191, 11, 45, // Opcode: SH_MM
/* 1113 */    MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 1125
/* 1117 */    MCD::OPC_CheckPredicate, 3, 238, 1, // Skip to: 1615
/* 1121 */    MCD::OPC_Decode, 166, 7, 45, // Opcode: LH_MM
/* 1125 */    MCD::OPC_FilterValue, 16, 207, 0, // Skip to: 1336
/* 1129 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 1132 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 1144
/* 1136 */    MCD::OPC_CheckPredicate, 3, 219, 1, // Skip to: 1615
/* 1140 */    MCD::OPC_Decode, 250, 1, 48, // Opcode: BLTZ_MM
/* 1144 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 1156
/* 1148 */    MCD::OPC_CheckPredicate, 3, 207, 1, // Skip to: 1615
/* 1152 */    MCD::OPC_Decode, 247, 1, 48, // Opcode: BLTZAL_MM
/* 1156 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 1168
/* 1160 */    MCD::OPC_CheckPredicate, 3, 195, 1, // Skip to: 1615
/* 1164 */    MCD::OPC_Decode, 208, 1, 48, // Opcode: BGEZ_MM
/* 1168 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 1180
/* 1172 */    MCD::OPC_CheckPredicate, 3, 183, 1, // Skip to: 1615
/* 1176 */    MCD::OPC_Decode, 205, 1, 48, // Opcode: BGEZAL_MM
/* 1180 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 1192
/* 1184 */    MCD::OPC_CheckPredicate, 3, 171, 1, // Skip to: 1615
/* 1188 */    MCD::OPC_Decode, 238, 1, 48, // Opcode: BLEZ_MM
/* 1192 */    MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 1204
/* 1196 */    MCD::OPC_CheckPredicate, 3, 159, 1, // Skip to: 1615
/* 1200 */    MCD::OPC_Decode, 142, 2, 48, // Opcode: BNEZC_MM
/* 1204 */    MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 1216
/* 1208 */    MCD::OPC_CheckPredicate, 3, 147, 1, // Skip to: 1615
/* 1212 */    MCD::OPC_Decode, 214, 1, 48, // Opcode: BGTZ_MM
/* 1216 */    MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 1228
/* 1220 */    MCD::OPC_CheckPredicate, 3, 135, 1, // Skip to: 1615
/* 1224 */    MCD::OPC_Decode, 195, 1, 48, // Opcode: BEQZC_MM
/* 1228 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 1240
/* 1232 */    MCD::OPC_CheckPredicate, 3, 123, 1, // Skip to: 1615
/* 1236 */    MCD::OPC_Decode, 179, 13, 49, // Opcode: TLTI_MM
/* 1240 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 1252
/* 1244 */    MCD::OPC_CheckPredicate, 3, 111, 1, // Skip to: 1615
/* 1248 */    MCD::OPC_Decode, 164, 13, 49, // Opcode: TGEI_MM
/* 1252 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 1264
/* 1256 */    MCD::OPC_CheckPredicate, 3, 99, 1, // Skip to: 1615
/* 1260 */    MCD::OPC_Decode, 178, 13, 49, // Opcode: TLTIU_MM
/* 1264 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 1276
/* 1268 */    MCD::OPC_CheckPredicate, 3, 87, 1, // Skip to: 1615
/* 1272 */    MCD::OPC_Decode, 163, 13, 49, // Opcode: TGEIU_MM
/* 1276 */    MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 1288
/* 1280 */    MCD::OPC_CheckPredicate, 3, 75, 1, // Skip to: 1615
/* 1284 */    MCD::OPC_Decode, 185, 13, 49, // Opcode: TNEI_MM
/* 1288 */    MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 1300
/* 1292 */    MCD::OPC_CheckPredicate, 3, 63, 1, // Skip to: 1615
/* 1296 */    MCD::OPC_Decode, 190, 7, 49, // Opcode: LUi_MM
/* 1300 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 1312
/* 1304 */    MCD::OPC_CheckPredicate, 3, 51, 1, // Skip to: 1615
/* 1308 */    MCD::OPC_Decode, 158, 13, 49, // Opcode: TEQI_MM
/* 1312 */    MCD::OPC_FilterValue, 17, 8, 0, // Skip to: 1324
/* 1316 */    MCD::OPC_CheckPredicate, 3, 39, 1, // Skip to: 1615
/* 1320 */    MCD::OPC_Decode, 246, 1, 48, // Opcode: BLTZALS_MM
/* 1324 */    MCD::OPC_FilterValue, 19, 31, 1, // Skip to: 1615
/* 1328 */    MCD::OPC_CheckPredicate, 3, 27, 1, // Skip to: 1615
/* 1332 */    MCD::OPC_Decode, 204, 1, 48, // Opcode: BGEZALS_MM
/* 1336 */    MCD::OPC_FilterValue, 20, 8, 0, // Skip to: 1348
/* 1340 */    MCD::OPC_CheckPredicate, 3, 15, 1, // Skip to: 1615
/* 1344 */    MCD::OPC_Decode, 247, 9, 50, // Opcode: ORi_MM
/* 1348 */    MCD::OPC_FilterValue, 21, 29, 0, // Skip to: 1381
/* 1352 */    MCD::OPC_ExtractField, 0, 13,  // Inst{12-0} ...
/* 1355 */    MCD::OPC_FilterValue, 251, 2, 8, 0, // Skip to: 1368
/* 1360 */    MCD::OPC_CheckPredicate, 3, 251, 0, // Skip to: 1615
/* 1364 */    MCD::OPC_Decode, 216, 8, 51, // Opcode: MOVF_I_MM
/* 1368 */    MCD::OPC_FilterValue, 251, 18, 242, 0, // Skip to: 1615
/* 1373 */    MCD::OPC_CheckPredicate, 3, 238, 0, // Skip to: 1615
/* 1377 */    MCD::OPC_Decode, 236, 8, 51, // Opcode: MOVT_I_MM
/* 1381 */    MCD::OPC_FilterValue, 24, 99, 0, // Skip to: 1484
/* 1385 */    MCD::OPC_ExtractField, 12, 4,  // Inst{15-12} ...
/* 1388 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 1400
/* 1392 */    MCD::OPC_CheckPredicate, 3, 219, 0, // Skip to: 1615
/* 1396 */    MCD::OPC_Decode, 201, 7, 46, // Opcode: LWL_MM
/* 1400 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 1412
/* 1404 */    MCD::OPC_CheckPredicate, 3, 207, 0, // Skip to: 1615
/* 1408 */    MCD::OPC_Decode, 208, 7, 46, // Opcode: LWR_MM
/* 1412 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 1424
/* 1416 */    MCD::OPC_CheckPredicate, 3, 195, 0, // Skip to: 1615
/* 1420 */    MCD::OPC_Decode, 157, 10, 47, // Opcode: PREF_MM
/* 1424 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 1436
/* 1428 */    MCD::OPC_CheckPredicate, 3, 183, 0, // Skip to: 1615
/* 1432 */    MCD::OPC_Decode, 174, 7, 46, // Opcode: LL_MM
/* 1436 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 1448
/* 1440 */    MCD::OPC_CheckPredicate, 3, 171, 0, // Skip to: 1615
/* 1444 */    MCD::OPC_Decode, 220, 12, 46, // Opcode: SWL_MM
/* 1448 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 1460
/* 1452 */    MCD::OPC_CheckPredicate, 3, 159, 0, // Skip to: 1615
/* 1456 */    MCD::OPC_Decode, 226, 12, 46, // Opcode: SWR_MM
/* 1460 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 1472
/* 1464 */    MCD::OPC_CheckPredicate, 3, 147, 0, // Skip to: 1615
/* 1468 */    MCD::OPC_Decode, 252, 10, 46, // Opcode: SC_MM
/* 1472 */    MCD::OPC_FilterValue, 14, 139, 0, // Skip to: 1615
/* 1476 */    MCD::OPC_CheckPredicate, 3, 135, 0, // Skip to: 1615
/* 1480 */    MCD::OPC_Decode, 211, 7, 46, // Opcode: LWU_MM
/* 1484 */    MCD::OPC_FilterValue, 28, 8, 0, // Skip to: 1496
/* 1488 */    MCD::OPC_CheckPredicate, 3, 123, 0, // Skip to: 1615
/* 1492 */    MCD::OPC_Decode, 221, 13, 50, // Opcode: XORi_MM
/* 1496 */    MCD::OPC_FilterValue, 29, 8, 0, // Skip to: 1508
/* 1500 */    MCD::OPC_CheckPredicate, 3, 111, 0, // Skip to: 1615
/* 1504 */    MCD::OPC_Decode, 239, 6, 52, // Opcode: JALS_MM
/* 1508 */    MCD::OPC_FilterValue, 36, 8, 0, // Skip to: 1520
/* 1512 */    MCD::OPC_CheckPredicate, 3, 99, 0, // Skip to: 1615
/* 1516 */    MCD::OPC_Decode, 220, 11, 44, // Opcode: SLTi_MM
/* 1520 */    MCD::OPC_FilterValue, 37, 8, 0, // Skip to: 1532
/* 1524 */    MCD::OPC_CheckPredicate, 3, 87, 0, // Skip to: 1615
/* 1528 */    MCD::OPC_Decode, 196, 1, 53, // Opcode: BEQ_MM
/* 1532 */    MCD::OPC_FilterValue, 44, 8, 0, // Skip to: 1544
/* 1536 */    MCD::OPC_CheckPredicate, 3, 75, 0, // Skip to: 1615
/* 1540 */    MCD::OPC_Decode, 223, 11, 44, // Opcode: SLTiu_MM
/* 1544 */    MCD::OPC_FilterValue, 45, 8, 0, // Skip to: 1556
/* 1548 */    MCD::OPC_CheckPredicate, 3, 63, 0, // Skip to: 1615
/* 1552 */    MCD::OPC_Decode, 143, 2, 53, // Opcode: BNE_MM
/* 1556 */    MCD::OPC_FilterValue, 52, 7, 0, // Skip to: 1567
/* 1560 */    MCD::OPC_CheckPredicate, 3, 51, 0, // Skip to: 1615
/* 1564 */    MCD::OPC_Decode, 94, 50, // Opcode: ANDi_MM
/* 1567 */    MCD::OPC_FilterValue, 53, 8, 0, // Skip to: 1579
/* 1571 */    MCD::OPC_CheckPredicate, 3, 40, 0, // Skip to: 1615
/* 1575 */    MCD::OPC_Decode, 252, 6, 52, // Opcode: J_MM
/* 1579 */    MCD::OPC_FilterValue, 61, 8, 0, // Skip to: 1591
/* 1583 */    MCD::OPC_CheckPredicate, 3, 28, 0, // Skip to: 1615
/* 1587 */    MCD::OPC_Decode, 241, 6, 52, // Opcode: JAL_MM
/* 1591 */    MCD::OPC_FilterValue, 62, 8, 0, // Skip to: 1603
/* 1595 */    MCD::OPC_CheckPredicate, 3, 16, 0, // Skip to: 1615
/* 1599 */    MCD::OPC_Decode, 230, 12, 45, // Opcode: SW_MM
/* 1603 */    MCD::OPC_FilterValue, 63, 8, 0, // Skip to: 1615
/* 1607 */    MCD::OPC_CheckPredicate, 3, 4, 0, // Skip to: 1615
/* 1611 */    MCD::OPC_Decode, 216, 7, 45, // Opcode: LW_MM
/* 1615 */    MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMips32[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 0, 173, 3, // Skip to: 948
/* 7 */       MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 10 */      MCD::OPC_FilterValue, 0, 54, 0, // Skip to: 68
/* 14 */      MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 17 */      MCD::OPC_FilterValue, 0, 20, 53, // Skip to: 13609
/* 21 */      MCD::OPC_ExtractField, 6, 15,  // Inst{20-6} ...
/* 24 */      MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 36
/* 28 */      MCD::OPC_CheckPredicate, 1, 28, 0, // Skip to: 60
/* 32 */      MCD::OPC_Decode, 155, 12, 0, // Opcode: SSNOP
/* 36 */      MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 48
/* 40 */      MCD::OPC_CheckPredicate, 1, 16, 0, // Skip to: 60
/* 44 */      MCD::OPC_Decode, 248, 4, 0, // Opcode: EHB
/* 48 */      MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 60
/* 52 */      MCD::OPC_CheckPredicate, 4, 4, 0, // Skip to: 60
/* 56 */      MCD::OPC_Decode, 250, 9, 0, // Opcode: PAUSE
/* 60 */      MCD::OPC_CheckPredicate, 5, 233, 52, // Skip to: 13609
/* 64 */      MCD::OPC_Decode, 200, 11, 54, // Opcode: SLL
/* 68 */      MCD::OPC_FilterValue, 1, 39, 0, // Skip to: 111
/* 72 */      MCD::OPC_ExtractField, 16, 2,  // Inst{17-16} ...
/* 75 */      MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 93
/* 79 */      MCD::OPC_CheckPredicate, 6, 214, 52, // Skip to: 13609
/* 83 */      MCD::OPC_CheckField, 6, 5, 0, 208, 52, // Skip to: 13609
/* 89 */      MCD::OPC_Decode, 214, 8, 55, // Opcode: MOVF_I
/* 93 */      MCD::OPC_FilterValue, 1, 200, 52, // Skip to: 13609
/* 97 */      MCD::OPC_CheckPredicate, 6, 196, 52, // Skip to: 13609
/* 101 */     MCD::OPC_CheckField, 6, 5, 0, 190, 52, // Skip to: 13609
/* 107 */     MCD::OPC_Decode, 234, 8, 55, // Opcode: MOVT_I
/* 111 */     MCD::OPC_FilterValue, 2, 27, 0, // Skip to: 142
/* 115 */     MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 118 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 130
/* 122 */     MCD::OPC_CheckPredicate, 5, 171, 52, // Skip to: 13609
/* 126 */     MCD::OPC_Decode, 134, 12, 54, // Opcode: SRL
/* 130 */     MCD::OPC_FilterValue, 1, 163, 52, // Skip to: 13609
/* 134 */     MCD::OPC_CheckPredicate, 4, 159, 52, // Skip to: 13609
/* 138 */     MCD::OPC_Decode, 222, 10, 54, // Opcode: ROTR
/* 142 */     MCD::OPC_FilterValue, 3, 14, 0, // Skip to: 160
/* 146 */     MCD::OPC_CheckPredicate, 1, 147, 52, // Skip to: 13609
/* 150 */     MCD::OPC_CheckField, 21, 5, 0, 141, 52, // Skip to: 13609
/* 156 */     MCD::OPC_Decode, 242, 11, 54, // Opcode: SRA
/* 160 */     MCD::OPC_FilterValue, 4, 14, 0, // Skip to: 178
/* 164 */     MCD::OPC_CheckPredicate, 1, 129, 52, // Skip to: 13609
/* 168 */     MCD::OPC_CheckField, 6, 5, 0, 123, 52, // Skip to: 13609
/* 174 */     MCD::OPC_Decode, 208, 11, 33, // Opcode: SLLV
/* 178 */     MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 196
/* 182 */     MCD::OPC_CheckPredicate, 7, 111, 52, // Skip to: 13609
/* 186 */     MCD::OPC_CheckField, 8, 3, 0, 105, 52, // Skip to: 13609
/* 192 */     MCD::OPC_Decode, 183, 7, 56, // Opcode: LSA
/* 196 */     MCD::OPC_FilterValue, 6, 27, 0, // Skip to: 227
/* 200 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 203 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 215
/* 207 */     MCD::OPC_CheckPredicate, 1, 86, 52, // Skip to: 13609
/* 211 */     MCD::OPC_Decode, 148, 12, 33, // Opcode: SRLV
/* 215 */     MCD::OPC_FilterValue, 1, 78, 52, // Skip to: 13609
/* 219 */     MCD::OPC_CheckPredicate, 4, 74, 52, // Skip to: 13609
/* 223 */     MCD::OPC_Decode, 223, 10, 33, // Opcode: ROTRV
/* 227 */     MCD::OPC_FilterValue, 7, 14, 0, // Skip to: 245
/* 231 */     MCD::OPC_CheckPredicate, 1, 62, 52, // Skip to: 13609
/* 235 */     MCD::OPC_CheckField, 6, 5, 0, 56, 52, // Skip to: 13609
/* 241 */     MCD::OPC_Decode, 255, 11, 33, // Opcode: SRAV
/* 245 */     MCD::OPC_FilterValue, 8, 27, 0, // Skip to: 276
/* 249 */     MCD::OPC_ExtractField, 6, 15,  // Inst{20-6} ...
/* 252 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 264
/* 256 */     MCD::OPC_CheckPredicate, 1, 37, 52, // Skip to: 13609
/* 260 */     MCD::OPC_Decode, 244, 6, 57, // Opcode: JR
/* 264 */     MCD::OPC_FilterValue, 16, 29, 52, // Skip to: 13609
/* 268 */     MCD::OPC_CheckPredicate, 8, 25, 52, // Skip to: 13609
/* 272 */     MCD::OPC_Decode, 249, 6, 57, // Opcode: JR_HB
/* 276 */     MCD::OPC_FilterValue, 9, 39, 0, // Skip to: 319
/* 280 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 283 */     MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 301
/* 287 */     MCD::OPC_CheckPredicate, 5, 6, 52, // Skip to: 13609
/* 291 */     MCD::OPC_CheckField, 16, 5, 0, 0, 52, // Skip to: 13609
/* 297 */     MCD::OPC_Decode, 230, 6, 58, // Opcode: JALR
/* 301 */     MCD::OPC_FilterValue, 16, 248, 51, // Skip to: 13609
/* 305 */     MCD::OPC_CheckPredicate, 9, 244, 51, // Skip to: 13609
/* 309 */     MCD::OPC_CheckField, 16, 5, 0, 238, 51, // Skip to: 13609
/* 315 */     MCD::OPC_Decode, 237, 6, 58, // Opcode: JALR_HB
/* 319 */     MCD::OPC_FilterValue, 10, 14, 0, // Skip to: 337
/* 323 */     MCD::OPC_CheckPredicate, 6, 226, 51, // Skip to: 13609
/* 327 */     MCD::OPC_CheckField, 6, 5, 0, 220, 51, // Skip to: 13609
/* 333 */     MCD::OPC_Decode, 246, 8, 59, // Opcode: MOVZ_I_I
/* 337 */     MCD::OPC_FilterValue, 11, 14, 0, // Skip to: 355
/* 341 */     MCD::OPC_CheckPredicate, 6, 208, 51, // Skip to: 13609
/* 345 */     MCD::OPC_CheckField, 6, 5, 0, 202, 51, // Skip to: 13609
/* 351 */     MCD::OPC_Decode, 226, 8, 59, // Opcode: MOVN_I_I
/* 355 */     MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 367
/* 359 */     MCD::OPC_CheckPredicate, 1, 190, 51, // Skip to: 13609
/* 363 */     MCD::OPC_Decode, 234, 12, 60, // Opcode: SYSCALL
/* 367 */     MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 379
/* 371 */     MCD::OPC_CheckPredicate, 1, 178, 51, // Skip to: 13609
/* 375 */     MCD::OPC_Decode, 153, 2, 30, // Opcode: BREAK
/* 379 */     MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 391
/* 383 */     MCD::OPC_CheckPredicate, 9, 166, 51, // Skip to: 13609
/* 387 */     MCD::OPC_Decode, 231, 12, 61, // Opcode: SYNC
/* 391 */     MCD::OPC_FilterValue, 16, 43, 0, // Skip to: 438
/* 395 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 398 */     MCD::OPC_FilterValue, 0, 151, 51, // Skip to: 13609
/* 402 */     MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 405 */     MCD::OPC_FilterValue, 0, 144, 51, // Skip to: 13609
/* 409 */     MCD::OPC_ExtractField, 23, 3,  // Inst{25-23} ...
/* 412 */     MCD::OPC_FilterValue, 0, 137, 51, // Skip to: 13609
/* 416 */     MCD::OPC_CheckPredicate, 10, 10, 0, // Skip to: 430
/* 420 */     MCD::OPC_CheckField, 21, 2, 0, 4, 0, // Skip to: 430
/* 426 */     MCD::OPC_Decode, 162, 8, 62, // Opcode: MFHI
/* 430 */     MCD::OPC_CheckPredicate, 11, 119, 51, // Skip to: 13609
/* 434 */     MCD::OPC_Decode, 165, 8, 63, // Opcode: MFHI_DSP
/* 438 */     MCD::OPC_FilterValue, 17, 36, 0, // Skip to: 478
/* 442 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 445 */     MCD::OPC_FilterValue, 0, 104, 51, // Skip to: 13609
/* 449 */     MCD::OPC_ExtractField, 13, 8,  // Inst{20-13} ...
/* 452 */     MCD::OPC_FilterValue, 0, 97, 51, // Skip to: 13609
/* 456 */     MCD::OPC_CheckPredicate, 12, 10, 0, // Skip to: 470
/* 460 */     MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 470
/* 466 */     MCD::OPC_Decode, 151, 9, 57, // Opcode: MTHI
/* 470 */     MCD::OPC_CheckPredicate, 11, 79, 51, // Skip to: 13609
/* 474 */     MCD::OPC_Decode, 153, 9, 64, // Opcode: MTHI_DSP
/* 478 */     MCD::OPC_FilterValue, 18, 43, 0, // Skip to: 525
/* 482 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 485 */     MCD::OPC_FilterValue, 0, 64, 51, // Skip to: 13609
/* 489 */     MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 492 */     MCD::OPC_FilterValue, 0, 57, 51, // Skip to: 13609
/* 496 */     MCD::OPC_ExtractField, 23, 3,  // Inst{25-23} ...
/* 499 */     MCD::OPC_FilterValue, 0, 50, 51, // Skip to: 13609
/* 503 */     MCD::OPC_CheckPredicate, 10, 10, 0, // Skip to: 517
/* 507 */     MCD::OPC_CheckField, 21, 2, 0, 4, 0, // Skip to: 517
/* 513 */     MCD::OPC_Decode, 167, 8, 62, // Opcode: MFLO
/* 517 */     MCD::OPC_CheckPredicate, 11, 32, 51, // Skip to: 13609
/* 521 */     MCD::OPC_Decode, 170, 8, 63, // Opcode: MFLO_DSP
/* 525 */     MCD::OPC_FilterValue, 19, 36, 0, // Skip to: 565
/* 529 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 532 */     MCD::OPC_FilterValue, 0, 17, 51, // Skip to: 13609
/* 536 */     MCD::OPC_ExtractField, 13, 8,  // Inst{20-13} ...
/* 539 */     MCD::OPC_FilterValue, 0, 10, 51, // Skip to: 13609
/* 543 */     MCD::OPC_CheckPredicate, 12, 10, 0, // Skip to: 557
/* 547 */     MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 557
/* 553 */     MCD::OPC_Decode, 156, 9, 57, // Opcode: MTLO
/* 557 */     MCD::OPC_CheckPredicate, 11, 248, 50, // Skip to: 13609
/* 561 */     MCD::OPC_Decode, 158, 9, 65, // Opcode: MTLO_DSP
/* 565 */     MCD::OPC_FilterValue, 21, 14, 0, // Skip to: 583
/* 569 */     MCD::OPC_CheckPredicate, 13, 236, 50, // Skip to: 13609
/* 573 */     MCD::OPC_CheckField, 8, 3, 0, 230, 50, // Skip to: 13609
/* 579 */     MCD::OPC_Decode, 175, 4, 66, // Opcode: DLSA
/* 583 */     MCD::OPC_FilterValue, 24, 36, 0, // Skip to: 623
/* 587 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 590 */     MCD::OPC_FilterValue, 0, 215, 50, // Skip to: 13609
/* 594 */     MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 597 */     MCD::OPC_FilterValue, 0, 208, 50, // Skip to: 13609
/* 601 */     MCD::OPC_CheckPredicate, 12, 10, 0, // Skip to: 615
/* 605 */     MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 615
/* 611 */     MCD::OPC_Decode, 181, 9, 40, // Opcode: MULT
/* 615 */     MCD::OPC_CheckPredicate, 11, 190, 50, // Skip to: 13609
/* 619 */     MCD::OPC_Decode, 183, 9, 67, // Opcode: MULT_DSP
/* 623 */     MCD::OPC_FilterValue, 25, 36, 0, // Skip to: 663
/* 627 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 630 */     MCD::OPC_FilterValue, 0, 175, 50, // Skip to: 13609
/* 634 */     MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 637 */     MCD::OPC_FilterValue, 0, 168, 50, // Skip to: 13609
/* 641 */     MCD::OPC_CheckPredicate, 12, 10, 0, // Skip to: 655
/* 645 */     MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 655
/* 651 */     MCD::OPC_Decode, 185, 9, 40, // Opcode: MULTu
/* 655 */     MCD::OPC_CheckPredicate, 11, 150, 50, // Skip to: 13609
/* 659 */     MCD::OPC_Decode, 182, 9, 67, // Opcode: MULTU_DSP
/* 663 */     MCD::OPC_FilterValue, 26, 14, 0, // Skip to: 681
/* 667 */     MCD::OPC_CheckPredicate, 12, 138, 50, // Skip to: 13609
/* 671 */     MCD::OPC_CheckField, 6, 10, 0, 132, 50, // Skip to: 13609
/* 677 */     MCD::OPC_Decode, 137, 11, 40, // Opcode: SDIV
/* 681 */     MCD::OPC_FilterValue, 27, 14, 0, // Skip to: 699
/* 685 */     MCD::OPC_CheckPredicate, 12, 120, 50, // Skip to: 13609
/* 689 */     MCD::OPC_CheckField, 6, 10, 0, 114, 50, // Skip to: 13609
/* 695 */     MCD::OPC_Decode, 196, 13, 40, // Opcode: UDIV
/* 699 */     MCD::OPC_FilterValue, 32, 13, 0, // Skip to: 716
/* 703 */     MCD::OPC_CheckPredicate, 1, 102, 50, // Skip to: 13609
/* 707 */     MCD::OPC_CheckField, 6, 5, 0, 96, 50, // Skip to: 13609
/* 713 */     MCD::OPC_Decode, 25, 32, // Opcode: ADD
/* 716 */     MCD::OPC_FilterValue, 33, 13, 0, // Skip to: 733
/* 720 */     MCD::OPC_CheckPredicate, 1, 85, 50, // Skip to: 13609
/* 724 */     MCD::OPC_CheckField, 6, 5, 0, 79, 50, // Skip to: 13609
/* 730 */     MCD::OPC_Decode, 76, 32, // Opcode: ADDu
/* 733 */     MCD::OPC_FilterValue, 34, 14, 0, // Skip to: 751
/* 737 */     MCD::OPC_CheckPredicate, 1, 68, 50, // Skip to: 13609
/* 741 */     MCD::OPC_CheckField, 6, 5, 0, 62, 50, // Skip to: 13609
/* 747 */     MCD::OPC_Decode, 165, 12, 32, // Opcode: SUB
/* 751 */     MCD::OPC_FilterValue, 35, 14, 0, // Skip to: 769
/* 755 */     MCD::OPC_CheckPredicate, 1, 50, 50, // Skip to: 13609
/* 759 */     MCD::OPC_CheckField, 6, 5, 0, 44, 50, // Skip to: 13609
/* 765 */     MCD::OPC_Decode, 205, 12, 32, // Opcode: SUBu
/* 769 */     MCD::OPC_FilterValue, 36, 13, 0, // Skip to: 786
/* 773 */     MCD::OPC_CheckPredicate, 1, 32, 50, // Skip to: 13609
/* 777 */     MCD::OPC_CheckField, 6, 5, 0, 26, 50, // Skip to: 13609
/* 783 */     MCD::OPC_Decode, 82, 32, // Opcode: AND
/* 786 */     MCD::OPC_FilterValue, 37, 14, 0, // Skip to: 804
/* 790 */     MCD::OPC_CheckPredicate, 1, 15, 50, // Skip to: 13609
/* 794 */     MCD::OPC_CheckField, 6, 5, 0, 9, 50, // Skip to: 13609
/* 800 */     MCD::OPC_Decode, 236, 9, 32, // Opcode: OR
/* 804 */     MCD::OPC_FilterValue, 38, 14, 0, // Skip to: 822
/* 808 */     MCD::OPC_CheckPredicate, 1, 253, 49, // Skip to: 13609
/* 812 */     MCD::OPC_CheckField, 6, 5, 0, 247, 49, // Skip to: 13609
/* 818 */     MCD::OPC_Decode, 210, 13, 32, // Opcode: XOR
/* 822 */     MCD::OPC_FilterValue, 39, 14, 0, // Skip to: 840
/* 826 */     MCD::OPC_CheckPredicate, 1, 235, 49, // Skip to: 13609
/* 830 */     MCD::OPC_CheckField, 6, 5, 0, 229, 49, // Skip to: 13609
/* 836 */     MCD::OPC_Decode, 225, 9, 32, // Opcode: NOR
/* 840 */     MCD::OPC_FilterValue, 42, 14, 0, // Skip to: 858
/* 844 */     MCD::OPC_CheckPredicate, 1, 217, 49, // Skip to: 13609
/* 848 */     MCD::OPC_CheckField, 6, 5, 0, 211, 49, // Skip to: 13609
/* 854 */     MCD::OPC_Decode, 215, 11, 32, // Opcode: SLT
/* 858 */     MCD::OPC_FilterValue, 43, 14, 0, // Skip to: 876
/* 862 */     MCD::OPC_CheckPredicate, 1, 199, 49, // Skip to: 13609
/* 866 */     MCD::OPC_CheckField, 6, 5, 0, 193, 49, // Skip to: 13609
/* 872 */     MCD::OPC_Decode, 224, 11, 32, // Opcode: SLTu
/* 876 */     MCD::OPC_FilterValue, 48, 8, 0, // Skip to: 888
/* 880 */     MCD::OPC_CheckPredicate, 2, 181, 49, // Skip to: 13609
/* 884 */     MCD::OPC_Decode, 160, 13, 68, // Opcode: TGE
/* 888 */     MCD::OPC_FilterValue, 49, 8, 0, // Skip to: 900
/* 892 */     MCD::OPC_CheckPredicate, 2, 169, 49, // Skip to: 13609
/* 896 */     MCD::OPC_Decode, 165, 13, 68, // Opcode: TGEU
/* 900 */     MCD::OPC_FilterValue, 50, 8, 0, // Skip to: 912
/* 904 */     MCD::OPC_CheckPredicate, 2, 157, 49, // Skip to: 13609
/* 908 */     MCD::OPC_Decode, 176, 13, 68, // Opcode: TLT
/* 912 */     MCD::OPC_FilterValue, 51, 8, 0, // Skip to: 924
/* 916 */     MCD::OPC_CheckPredicate, 2, 145, 49, // Skip to: 13609
/* 920 */     MCD::OPC_Decode, 180, 13, 68, // Opcode: TLTU
/* 924 */     MCD::OPC_FilterValue, 52, 8, 0, // Skip to: 936
/* 928 */     MCD::OPC_CheckPredicate, 2, 133, 49, // Skip to: 13609
/* 932 */     MCD::OPC_Decode, 156, 13, 68, // Opcode: TEQ
/* 936 */     MCD::OPC_FilterValue, 54, 125, 49, // Skip to: 13609
/* 940 */     MCD::OPC_CheckPredicate, 2, 121, 49, // Skip to: 13609
/* 944 */     MCD::OPC_Decode, 183, 13, 68, // Opcode: TNE
/* 948 */     MCD::OPC_FilterValue, 1, 201, 0, // Skip to: 1153
/* 952 */     MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 955 */     MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 967
/* 959 */     MCD::OPC_CheckPredicate, 1, 102, 49, // Skip to: 13609
/* 963 */     MCD::OPC_Decode, 241, 1, 69, // Opcode: BLTZ
/* 967 */     MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 979
/* 971 */     MCD::OPC_CheckPredicate, 1, 90, 49, // Skip to: 13609
/* 975 */     MCD::OPC_Decode, 199, 1, 69, // Opcode: BGEZ
/* 979 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 991
/* 983 */     MCD::OPC_CheckPredicate, 14, 78, 49, // Skip to: 13609
/* 987 */     MCD::OPC_Decode, 249, 1, 69, // Opcode: BLTZL
/* 991 */     MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 1003
/* 995 */     MCD::OPC_CheckPredicate, 14, 66, 49, // Skip to: 13609
/* 999 */     MCD::OPC_Decode, 207, 1, 69, // Opcode: BGEZL
/* 1003 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 1015
/* 1007 */    MCD::OPC_CheckPredicate, 14, 54, 49, // Skip to: 13609
/* 1011 */    MCD::OPC_Decode, 161, 13, 70, // Opcode: TGEI
/* 1015 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 1027
/* 1019 */    MCD::OPC_CheckPredicate, 14, 42, 49, // Skip to: 13609
/* 1023 */    MCD::OPC_Decode, 162, 13, 70, // Opcode: TGEIU
/* 1027 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 1039
/* 1031 */    MCD::OPC_CheckPredicate, 14, 30, 49, // Skip to: 13609
/* 1035 */    MCD::OPC_Decode, 177, 13, 70, // Opcode: TLTI
/* 1039 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 1051
/* 1043 */    MCD::OPC_CheckPredicate, 14, 18, 49, // Skip to: 13609
/* 1047 */    MCD::OPC_Decode, 195, 13, 70, // Opcode: TTLTIU
/* 1051 */    MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 1063
/* 1055 */    MCD::OPC_CheckPredicate, 14, 6, 49, // Skip to: 13609
/* 1059 */    MCD::OPC_Decode, 157, 13, 70, // Opcode: TEQI
/* 1063 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 1075
/* 1067 */    MCD::OPC_CheckPredicate, 14, 250, 48, // Skip to: 13609
/* 1071 */    MCD::OPC_Decode, 184, 13, 70, // Opcode: TNEI
/* 1075 */    MCD::OPC_FilterValue, 16, 8, 0, // Skip to: 1087
/* 1079 */    MCD::OPC_CheckPredicate, 12, 238, 48, // Skip to: 13609
/* 1083 */    MCD::OPC_Decode, 243, 1, 69, // Opcode: BLTZAL
/* 1087 */    MCD::OPC_FilterValue, 17, 8, 0, // Skip to: 1099
/* 1091 */    MCD::OPC_CheckPredicate, 12, 226, 48, // Skip to: 13609
/* 1095 */    MCD::OPC_Decode, 201, 1, 69, // Opcode: BGEZAL
/* 1099 */    MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 1111
/* 1103 */    MCD::OPC_CheckPredicate, 14, 214, 48, // Skip to: 13609
/* 1107 */    MCD::OPC_Decode, 245, 1, 69, // Opcode: BLTZALL
/* 1111 */    MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 1123
/* 1115 */    MCD::OPC_CheckPredicate, 14, 202, 48, // Skip to: 13609
/* 1119 */    MCD::OPC_Decode, 203, 1, 69, // Opcode: BGEZALL
/* 1123 */    MCD::OPC_FilterValue, 28, 14, 0, // Skip to: 1141
/* 1127 */    MCD::OPC_CheckPredicate, 11, 190, 48, // Skip to: 13609
/* 1131 */    MCD::OPC_CheckField, 21, 5, 0, 184, 48, // Skip to: 13609
/* 1137 */    MCD::OPC_Decode, 151, 2, 71, // Opcode: BPOSGE32
/* 1141 */    MCD::OPC_FilterValue, 31, 176, 48, // Skip to: 13609
/* 1145 */    MCD::OPC_CheckPredicate, 4, 172, 48, // Skip to: 13609
/* 1149 */    MCD::OPC_Decode, 232, 12, 72, // Opcode: SYNCI
/* 1153 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 1165
/* 1157 */    MCD::OPC_CheckPredicate, 9, 160, 48, // Skip to: 13609
/* 1161 */    MCD::OPC_Decode, 228, 6, 73, // Opcode: J
/* 1165 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 1177
/* 1169 */    MCD::OPC_CheckPredicate, 1, 148, 48, // Skip to: 13609
/* 1173 */    MCD::OPC_Decode, 229, 6, 73, // Opcode: JAL
/* 1177 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 1189
/* 1181 */    MCD::OPC_CheckPredicate, 1, 136, 48, // Skip to: 13609
/* 1185 */    MCD::OPC_Decode, 188, 1, 74, // Opcode: BEQ
/* 1189 */    MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 1201
/* 1193 */    MCD::OPC_CheckPredicate, 1, 124, 48, // Skip to: 13609
/* 1197 */    MCD::OPC_Decode, 255, 1, 74, // Opcode: BNE
/* 1201 */    MCD::OPC_FilterValue, 6, 14, 0, // Skip to: 1219
/* 1205 */    MCD::OPC_CheckPredicate, 1, 112, 48, // Skip to: 13609
/* 1209 */    MCD::OPC_CheckField, 16, 5, 0, 106, 48, // Skip to: 13609
/* 1215 */    MCD::OPC_Decode, 233, 1, 69, // Opcode: BLEZ
/* 1219 */    MCD::OPC_FilterValue, 7, 14, 0, // Skip to: 1237
/* 1223 */    MCD::OPC_CheckPredicate, 1, 94, 48, // Skip to: 13609
/* 1227 */    MCD::OPC_CheckField, 16, 5, 0, 88, 48, // Skip to: 13609
/* 1233 */    MCD::OPC_Decode, 209, 1, 69, // Opcode: BGTZ
/* 1237 */    MCD::OPC_FilterValue, 8, 7, 0, // Skip to: 1248
/* 1241 */    MCD::OPC_CheckPredicate, 12, 76, 48, // Skip to: 13609
/* 1245 */    MCD::OPC_Decode, 72, 75, // Opcode: ADDi
/* 1248 */    MCD::OPC_FilterValue, 9, 7, 0, // Skip to: 1259
/* 1252 */    MCD::OPC_CheckPredicate, 5, 65, 48, // Skip to: 13609
/* 1256 */    MCD::OPC_Decode, 74, 75, // Opcode: ADDiu
/* 1259 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 1271
/* 1263 */    MCD::OPC_CheckPredicate, 1, 54, 48, // Skip to: 13609
/* 1267 */    MCD::OPC_Decode, 218, 11, 75, // Opcode: SLTi
/* 1271 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 1283
/* 1275 */    MCD::OPC_CheckPredicate, 1, 42, 48, // Skip to: 13609
/* 1279 */    MCD::OPC_Decode, 221, 11, 75, // Opcode: SLTiu
/* 1283 */    MCD::OPC_FilterValue, 12, 7, 0, // Skip to: 1294
/* 1287 */    MCD::OPC_CheckPredicate, 5, 30, 48, // Skip to: 13609
/* 1291 */    MCD::OPC_Decode, 92, 76, // Opcode: ANDi
/* 1294 */    MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 1306
/* 1298 */    MCD::OPC_CheckPredicate, 1, 19, 48, // Skip to: 13609
/* 1302 */    MCD::OPC_Decode, 245, 9, 76, // Opcode: ORi
/* 1306 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 1318
/* 1310 */    MCD::OPC_CheckPredicate, 1, 7, 48, // Skip to: 13609
/* 1314 */    MCD::OPC_Decode, 219, 13, 76, // Opcode: XORi
/* 1318 */    MCD::OPC_FilterValue, 15, 14, 0, // Skip to: 1336
/* 1322 */    MCD::OPC_CheckPredicate, 1, 251, 47, // Skip to: 13609
/* 1326 */    MCD::OPC_CheckField, 21, 5, 0, 245, 47, // Skip to: 13609
/* 1332 */    MCD::OPC_Decode, 188, 7, 49, // Opcode: LUi
/* 1336 */    MCD::OPC_FilterValue, 16, 248, 0, // Skip to: 1588
/* 1340 */    MCD::OPC_ExtractField, 3, 8,  // Inst{10-3} ...
/* 1343 */    MCD::OPC_FilterValue, 0, 112, 0, // Skip to: 1459
/* 1347 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 1350 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 1362
/* 1354 */    MCD::OPC_CheckPredicate, 9, 219, 47, // Skip to: 13609
/* 1358 */    MCD::OPC_Decode, 155, 8, 77, // Opcode: MFC0
/* 1362 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 1374
/* 1366 */    MCD::OPC_CheckPredicate, 9, 207, 47, // Skip to: 13609
/* 1370 */    MCD::OPC_Decode, 144, 9, 77, // Opcode: MTC0
/* 1374 */    MCD::OPC_FilterValue, 11, 20, 0, // Skip to: 1398
/* 1378 */    MCD::OPC_CheckPredicate, 4, 195, 47, // Skip to: 13609
/* 1382 */    MCD::OPC_CheckField, 11, 5, 12, 189, 47, // Skip to: 13609
/* 1388 */    MCD::OPC_CheckField, 0, 3, 0, 183, 47, // Skip to: 13609
/* 1394 */    MCD::OPC_Decode, 160, 4, 39, // Opcode: DI
/* 1398 */    MCD::OPC_FilterValue, 16, 175, 47, // Skip to: 13609
/* 1402 */    MCD::OPC_ExtractField, 0, 3,  // Inst{2-0} ...
/* 1405 */    MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 1423
/* 1409 */    MCD::OPC_CheckPredicate, 1, 164, 47, // Skip to: 13609
/* 1413 */    MCD::OPC_CheckField, 11, 10, 0, 158, 47, // Skip to: 13609
/* 1419 */    MCD::OPC_Decode, 170, 13, 0, // Opcode: TLBR
/* 1423 */    MCD::OPC_FilterValue, 2, 14, 0, // Skip to: 1441
/* 1427 */    MCD::OPC_CheckPredicate, 1, 146, 47, // Skip to: 13609
/* 1431 */    MCD::OPC_CheckField, 11, 10, 0, 140, 47, // Skip to: 13609
/* 1437 */    MCD::OPC_Decode, 172, 13, 0, // Opcode: TLBWI
/* 1441 */    MCD::OPC_FilterValue, 6, 132, 47, // Skip to: 13609
/* 1445 */    MCD::OPC_CheckPredicate, 1, 128, 47, // Skip to: 13609
/* 1449 */    MCD::OPC_CheckField, 11, 10, 0, 122, 47, // Skip to: 13609
/* 1455 */    MCD::OPC_Decode, 174, 13, 0, // Opcode: TLBWR
/* 1459 */    MCD::OPC_FilterValue, 1, 22, 0, // Skip to: 1485
/* 1463 */    MCD::OPC_CheckPredicate, 1, 110, 47, // Skip to: 13609
/* 1467 */    MCD::OPC_CheckField, 11, 15, 128, 128, 1, 102, 47, // Skip to: 13609
/* 1475 */    MCD::OPC_CheckField, 0, 3, 0, 96, 47, // Skip to: 13609
/* 1481 */    MCD::OPC_Decode, 168, 13, 0, // Opcode: TLBP
/* 1485 */    MCD::OPC_FilterValue, 3, 43, 0, // Skip to: 1532
/* 1489 */    MCD::OPC_ExtractField, 0, 3,  // Inst{2-0} ...
/* 1492 */    MCD::OPC_FilterValue, 0, 16, 0, // Skip to: 1512
/* 1496 */    MCD::OPC_CheckPredicate, 15, 77, 47, // Skip to: 13609
/* 1500 */    MCD::OPC_CheckField, 11, 15, 128, 128, 1, 69, 47, // Skip to: 13609
/* 1508 */    MCD::OPC_Decode, 252, 4, 0, // Opcode: ERET
/* 1512 */    MCD::OPC_FilterValue, 7, 61, 47, // Skip to: 13609
/* 1516 */    MCD::OPC_CheckPredicate, 9, 57, 47, // Skip to: 13609
/* 1520 */    MCD::OPC_CheckField, 11, 15, 128, 128, 1, 49, 47, // Skip to: 13609
/* 1528 */    MCD::OPC_Decode, 155, 4, 0, // Opcode: DERET
/* 1532 */    MCD::OPC_FilterValue, 4, 41, 47, // Skip to: 13609
/* 1536 */    MCD::OPC_ExtractField, 11, 5,  // Inst{15-11} ...
/* 1539 */    MCD::OPC_FilterValue, 0, 21, 0, // Skip to: 1564
/* 1543 */    MCD::OPC_CheckPredicate, 16, 30, 47, // Skip to: 13609
/* 1547 */    MCD::OPC_CheckField, 16, 10, 128, 4, 23, 47, // Skip to: 13609
/* 1554 */    MCD::OPC_CheckField, 0, 3, 0, 17, 47, // Skip to: 13609
/* 1560 */    MCD::OPC_Decode, 205, 13, 0, // Opcode: WAIT
/* 1564 */    MCD::OPC_FilterValue, 12, 9, 47, // Skip to: 13609
/* 1568 */    MCD::OPC_CheckPredicate, 4, 5, 47, // Skip to: 13609
/* 1572 */    MCD::OPC_CheckField, 21, 5, 11, 255, 46, // Skip to: 13609
/* 1578 */    MCD::OPC_CheckField, 0, 3, 0, 249, 46, // Skip to: 13609
/* 1584 */    MCD::OPC_Decode, 250, 4, 39, // Opcode: EI
/* 1588 */    MCD::OPC_FilterValue, 17, 21, 6, // Skip to: 3149
/* 1592 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 1595 */    MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 1613
/* 1599 */    MCD::OPC_CheckPredicate, 1, 230, 46, // Skip to: 13609
/* 1603 */    MCD::OPC_CheckField, 0, 11, 0, 224, 46, // Skip to: 13609
/* 1609 */    MCD::OPC_Decode, 156, 8, 78, // Opcode: MFC1
/* 1613 */    MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 1631
/* 1617 */    MCD::OPC_CheckPredicate, 17, 212, 46, // Skip to: 13609
/* 1621 */    MCD::OPC_CheckField, 0, 11, 0, 206, 46, // Skip to: 13609
/* 1627 */    MCD::OPC_Decode, 178, 4, 79, // Opcode: DMFC1
/* 1631 */    MCD::OPC_FilterValue, 2, 14, 0, // Skip to: 1649
/* 1635 */    MCD::OPC_CheckPredicate, 1, 194, 46, // Skip to: 13609
/* 1639 */    MCD::OPC_CheckField, 0, 11, 0, 188, 46, // Skip to: 13609
/* 1645 */    MCD::OPC_Decode, 219, 2, 80, // Opcode: CFC1
/* 1649 */    MCD::OPC_FilterValue, 3, 14, 0, // Skip to: 1667
/* 1653 */    MCD::OPC_CheckPredicate, 18, 176, 46, // Skip to: 13609
/* 1657 */    MCD::OPC_CheckField, 0, 11, 0, 170, 46, // Skip to: 13609
/* 1663 */    MCD::OPC_Decode, 159, 8, 81, // Opcode: MFHC1_D32
/* 1667 */    MCD::OPC_FilterValue, 4, 14, 0, // Skip to: 1685
/* 1671 */    MCD::OPC_CheckPredicate, 1, 158, 46, // Skip to: 13609
/* 1675 */    MCD::OPC_CheckField, 0, 11, 0, 152, 46, // Skip to: 13609
/* 1681 */    MCD::OPC_Decode, 145, 9, 82, // Opcode: MTC1
/* 1685 */    MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 1703
/* 1689 */    MCD::OPC_CheckPredicate, 17, 140, 46, // Skip to: 13609
/* 1693 */    MCD::OPC_CheckField, 0, 11, 0, 134, 46, // Skip to: 13609
/* 1699 */    MCD::OPC_Decode, 183, 4, 83, // Opcode: DMTC1
/* 1703 */    MCD::OPC_FilterValue, 6, 14, 0, // Skip to: 1721
/* 1707 */    MCD::OPC_CheckPredicate, 1, 122, 46, // Skip to: 13609
/* 1711 */    MCD::OPC_CheckField, 0, 11, 0, 116, 46, // Skip to: 13609
/* 1717 */    MCD::OPC_Decode, 191, 3, 84, // Opcode: CTC1
/* 1721 */    MCD::OPC_FilterValue, 7, 14, 0, // Skip to: 1739
/* 1725 */    MCD::OPC_CheckPredicate, 18, 104, 46, // Skip to: 13609
/* 1729 */    MCD::OPC_CheckField, 0, 11, 0, 98, 46, // Skip to: 13609
/* 1735 */    MCD::OPC_Decode, 148, 9, 85, // Opcode: MTHC1_D32
/* 1739 */    MCD::OPC_FilterValue, 8, 51, 0, // Skip to: 1794
/* 1743 */    MCD::OPC_ExtractField, 16, 2,  // Inst{17-16} ...
/* 1746 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 1758
/* 1750 */    MCD::OPC_CheckPredicate, 12, 79, 46, // Skip to: 13609
/* 1754 */    MCD::OPC_Decode, 171, 1, 86, // Opcode: BC1F
/* 1758 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 1770
/* 1762 */    MCD::OPC_CheckPredicate, 12, 67, 46, // Skip to: 13609
/* 1766 */    MCD::OPC_Decode, 175, 1, 86, // Opcode: BC1T
/* 1770 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 1782
/* 1774 */    MCD::OPC_CheckPredicate, 14, 55, 46, // Skip to: 13609
/* 1778 */    MCD::OPC_Decode, 172, 1, 86, // Opcode: BC1FL
/* 1782 */    MCD::OPC_FilterValue, 3, 47, 46, // Skip to: 13609
/* 1786 */    MCD::OPC_CheckPredicate, 14, 43, 46, // Skip to: 13609
/* 1790 */    MCD::OPC_Decode, 176, 1, 86, // Opcode: BC1TL
/* 1794 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 1806
/* 1798 */    MCD::OPC_CheckPredicate, 7, 31, 46, // Skip to: 13609
/* 1802 */    MCD::OPC_Decode, 174, 2, 87, // Opcode: BZ_V
/* 1806 */    MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 1818
/* 1810 */    MCD::OPC_CheckPredicate, 7, 19, 46, // Skip to: 13609
/* 1814 */    MCD::OPC_Decode, 148, 2, 87, // Opcode: BNZ_V
/* 1818 */    MCD::OPC_FilterValue, 16, 80, 2, // Skip to: 2414
/* 1822 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 1825 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 1837
/* 1829 */    MCD::OPC_CheckPredicate, 1, 0, 46, // Skip to: 13609
/* 1833 */    MCD::OPC_Decode, 155, 5, 88, // Opcode: FADD_S
/* 1837 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 1849
/* 1841 */    MCD::OPC_CheckPredicate, 1, 244, 45, // Skip to: 13609
/* 1845 */    MCD::OPC_Decode, 157, 6, 88, // Opcode: FSUB_S
/* 1849 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 1861
/* 1853 */    MCD::OPC_CheckPredicate, 1, 232, 45, // Skip to: 13609
/* 1857 */    MCD::OPC_Decode, 248, 5, 88, // Opcode: FMUL_S
/* 1861 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 1873
/* 1865 */    MCD::OPC_CheckPredicate, 1, 220, 45, // Skip to: 13609
/* 1869 */    MCD::OPC_Decode, 191, 5, 88, // Opcode: FDIV_S
/* 1873 */    MCD::OPC_FilterValue, 4, 14, 0, // Skip to: 1891
/* 1877 */    MCD::OPC_CheckPredicate, 2, 208, 45, // Skip to: 13609
/* 1881 */    MCD::OPC_CheckField, 16, 5, 0, 202, 45, // Skip to: 13609
/* 1887 */    MCD::OPC_Decode, 150, 6, 89, // Opcode: FSQRT_S
/* 1891 */    MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 1909
/* 1895 */    MCD::OPC_CheckPredicate, 1, 190, 45, // Skip to: 13609
/* 1899 */    MCD::OPC_CheckField, 16, 5, 0, 184, 45, // Skip to: 13609
/* 1905 */    MCD::OPC_Decode, 148, 5, 89, // Opcode: FABS_S
/* 1909 */    MCD::OPC_FilterValue, 6, 14, 0, // Skip to: 1927
/* 1913 */    MCD::OPC_CheckPredicate, 1, 172, 45, // Skip to: 13609
/* 1917 */    MCD::OPC_CheckField, 16, 5, 0, 166, 45, // Skip to: 13609
/* 1923 */    MCD::OPC_Decode, 240, 5, 89, // Opcode: FMOV_S
/* 1927 */    MCD::OPC_FilterValue, 7, 14, 0, // Skip to: 1945
/* 1931 */    MCD::OPC_CheckPredicate, 1, 154, 45, // Skip to: 13609
/* 1935 */    MCD::OPC_CheckField, 16, 5, 0, 148, 45, // Skip to: 13609
/* 1941 */    MCD::OPC_Decode, 254, 5, 89, // Opcode: FNEG_S
/* 1945 */    MCD::OPC_FilterValue, 12, 14, 0, // Skip to: 1963
/* 1949 */    MCD::OPC_CheckPredicate, 2, 136, 45, // Skip to: 13609
/* 1953 */    MCD::OPC_CheckField, 16, 5, 0, 130, 45, // Skip to: 13609
/* 1959 */    MCD::OPC_Decode, 231, 10, 89, // Opcode: ROUND_W_S
/* 1963 */    MCD::OPC_FilterValue, 13, 14, 0, // Skip to: 1981
/* 1967 */    MCD::OPC_CheckPredicate, 2, 118, 45, // Skip to: 13609
/* 1971 */    MCD::OPC_CheckField, 16, 5, 0, 112, 45, // Skip to: 13609
/* 1977 */    MCD::OPC_Decode, 193, 13, 89, // Opcode: TRUNC_W_S
/* 1981 */    MCD::OPC_FilterValue, 14, 14, 0, // Skip to: 1999
/* 1985 */    MCD::OPC_CheckPredicate, 2, 100, 45, // Skip to: 13609
/* 1989 */    MCD::OPC_CheckField, 16, 5, 0, 94, 45, // Skip to: 13609
/* 1995 */    MCD::OPC_Decode, 209, 2, 89, // Opcode: CEIL_W_S
/* 1999 */    MCD::OPC_FilterValue, 15, 14, 0, // Skip to: 2017
/* 2003 */    MCD::OPC_CheckPredicate, 2, 82, 45, // Skip to: 13609
/* 2007 */    MCD::OPC_CheckField, 16, 5, 0, 76, 45, // Skip to: 13609
/* 2013 */    MCD::OPC_Decode, 225, 5, 89, // Opcode: FLOOR_W_S
/* 2017 */    MCD::OPC_FilterValue, 17, 27, 0, // Skip to: 2048
/* 2021 */    MCD::OPC_ExtractField, 16, 2,  // Inst{17-16} ...
/* 2024 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 2036
/* 2028 */    MCD::OPC_CheckPredicate, 6, 57, 45, // Skip to: 13609
/* 2032 */    MCD::OPC_Decode, 217, 8, 90, // Opcode: MOVF_S
/* 2036 */    MCD::OPC_FilterValue, 1, 49, 45, // Skip to: 13609
/* 2040 */    MCD::OPC_CheckPredicate, 6, 45, 45, // Skip to: 13609
/* 2044 */    MCD::OPC_Decode, 237, 8, 90, // Opcode: MOVT_S
/* 2048 */    MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 2060
/* 2052 */    MCD::OPC_CheckPredicate, 6, 33, 45, // Skip to: 13609
/* 2056 */    MCD::OPC_Decode, 249, 8, 91, // Opcode: MOVZ_I_S
/* 2060 */    MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 2072
/* 2064 */    MCD::OPC_CheckPredicate, 6, 21, 45, // Skip to: 13609
/* 2068 */    MCD::OPC_Decode, 229, 8, 91, // Opcode: MOVN_I_S
/* 2072 */    MCD::OPC_FilterValue, 33, 14, 0, // Skip to: 2090
/* 2076 */    MCD::OPC_CheckPredicate, 19, 9, 45, // Skip to: 13609
/* 2080 */    MCD::OPC_CheckField, 16, 5, 0, 3, 45, // Skip to: 13609
/* 2086 */    MCD::OPC_Decode, 194, 3, 92, // Opcode: CVT_D32_S
/* 2090 */    MCD::OPC_FilterValue, 36, 14, 0, // Skip to: 2108
/* 2094 */    MCD::OPC_CheckPredicate, 1, 247, 44, // Skip to: 13609
/* 2098 */    MCD::OPC_CheckField, 16, 5, 0, 241, 44, // Skip to: 13609
/* 2104 */    MCD::OPC_Decode, 214, 3, 89, // Opcode: CVT_W_S
/* 2108 */    MCD::OPC_FilterValue, 37, 14, 0, // Skip to: 2126
/* 2112 */    MCD::OPC_CheckPredicate, 20, 229, 44, // Skip to: 13609
/* 2116 */    MCD::OPC_CheckField, 16, 5, 0, 223, 44, // Skip to: 13609
/* 2122 */    MCD::OPC_Decode, 203, 3, 93, // Opcode: CVT_L_S
/* 2126 */    MCD::OPC_FilterValue, 48, 14, 0, // Skip to: 2144
/* 2130 */    MCD::OPC_CheckPredicate, 12, 211, 44, // Skip to: 13609
/* 2134 */    MCD::OPC_CheckField, 6, 5, 0, 205, 44, // Skip to: 13609
/* 2140 */    MCD::OPC_Decode, 221, 3, 94, // Opcode: C_F_S
/* 2144 */    MCD::OPC_FilterValue, 49, 14, 0, // Skip to: 2162
/* 2148 */    MCD::OPC_CheckPredicate, 12, 193, 44, // Skip to: 13609
/* 2152 */    MCD::OPC_CheckField, 6, 5, 0, 187, 44, // Skip to: 13609
/* 2158 */    MCD::OPC_Decode, 135, 4, 94, // Opcode: C_UN_S
/* 2162 */    MCD::OPC_FilterValue, 50, 14, 0, // Skip to: 2180
/* 2166 */    MCD::OPC_CheckPredicate, 12, 175, 44, // Skip to: 13609
/* 2170 */    MCD::OPC_CheckField, 6, 5, 0, 169, 44, // Skip to: 13609
/* 2176 */    MCD::OPC_Decode, 218, 3, 94, // Opcode: C_EQ_S
/* 2180 */    MCD::OPC_FilterValue, 51, 14, 0, // Skip to: 2198
/* 2184 */    MCD::OPC_CheckPredicate, 12, 157, 44, // Skip to: 13609
/* 2188 */    MCD::OPC_CheckField, 6, 5, 0, 151, 44, // Skip to: 13609
/* 2194 */    MCD::OPC_Decode, 254, 3, 94, // Opcode: C_UEQ_S
/* 2198 */    MCD::OPC_FilterValue, 52, 14, 0, // Skip to: 2216
/* 2202 */    MCD::OPC_CheckPredicate, 12, 139, 44, // Skip to: 13609
/* 2206 */    MCD::OPC_CheckField, 6, 5, 0, 133, 44, // Skip to: 13609
/* 2212 */    MCD::OPC_Decode, 245, 3, 94, // Opcode: C_OLT_S
/* 2216 */    MCD::OPC_FilterValue, 53, 14, 0, // Skip to: 2234
/* 2220 */    MCD::OPC_CheckPredicate, 12, 121, 44, // Skip to: 13609
/* 2224 */    MCD::OPC_CheckField, 6, 5, 0, 115, 44, // Skip to: 13609
/* 2230 */    MCD::OPC_Decode, 132, 4, 94, // Opcode: C_ULT_S
/* 2234 */    MCD::OPC_FilterValue, 54, 14, 0, // Skip to: 2252
/* 2238 */    MCD::OPC_CheckPredicate, 12, 103, 44, // Skip to: 13609
/* 2242 */    MCD::OPC_CheckField, 6, 5, 0, 97, 44, // Skip to: 13609
/* 2248 */    MCD::OPC_Decode, 242, 3, 94, // Opcode: C_OLE_S
/* 2252 */    MCD::OPC_FilterValue, 55, 14, 0, // Skip to: 2270
/* 2256 */    MCD::OPC_CheckPredicate, 12, 85, 44, // Skip to: 13609
/* 2260 */    MCD::OPC_CheckField, 6, 5, 0, 79, 44, // Skip to: 13609
/* 2266 */    MCD::OPC_Decode, 129, 4, 94, // Opcode: C_ULE_S
/* 2270 */    MCD::OPC_FilterValue, 56, 14, 0, // Skip to: 2288
/* 2274 */    MCD::OPC_CheckPredicate, 12, 67, 44, // Skip to: 13609
/* 2278 */    MCD::OPC_CheckField, 6, 5, 0, 61, 44, // Skip to: 13609
/* 2284 */    MCD::OPC_Decode, 251, 3, 94, // Opcode: C_SF_S
/* 2288 */    MCD::OPC_FilterValue, 57, 14, 0, // Skip to: 2306
/* 2292 */    MCD::OPC_CheckPredicate, 12, 49, 44, // Skip to: 13609
/* 2296 */    MCD::OPC_CheckField, 6, 5, 0, 43, 44, // Skip to: 13609
/* 2302 */    MCD::OPC_Decode, 233, 3, 94, // Opcode: C_NGLE_S
/* 2306 */    MCD::OPC_FilterValue, 58, 14, 0, // Skip to: 2324
/* 2310 */    MCD::OPC_CheckPredicate, 12, 31, 44, // Skip to: 13609
/* 2314 */    MCD::OPC_CheckField, 6, 5, 0, 25, 44, // Skip to: 13609
/* 2320 */    MCD::OPC_Decode, 248, 3, 94, // Opcode: C_SEQ_S
/* 2324 */    MCD::OPC_FilterValue, 59, 14, 0, // Skip to: 2342
/* 2328 */    MCD::OPC_CheckPredicate, 12, 13, 44, // Skip to: 13609
/* 2332 */    MCD::OPC_CheckField, 6, 5, 0, 7, 44, // Skip to: 13609
/* 2338 */    MCD::OPC_Decode, 236, 3, 94, // Opcode: C_NGL_S
/* 2342 */    MCD::OPC_FilterValue, 60, 14, 0, // Skip to: 2360
/* 2346 */    MCD::OPC_CheckPredicate, 12, 251, 43, // Skip to: 13609
/* 2350 */    MCD::OPC_CheckField, 6, 5, 0, 245, 43, // Skip to: 13609
/* 2356 */    MCD::OPC_Decode, 227, 3, 94, // Opcode: C_LT_S
/* 2360 */    MCD::OPC_FilterValue, 61, 14, 0, // Skip to: 2378
/* 2364 */    MCD::OPC_CheckPredicate, 12, 233, 43, // Skip to: 13609
/* 2368 */    MCD::OPC_CheckField, 6, 5, 0, 227, 43, // Skip to: 13609
/* 2374 */    MCD::OPC_Decode, 230, 3, 94, // Opcode: C_NGE_S
/* 2378 */    MCD::OPC_FilterValue, 62, 14, 0, // Skip to: 2396
/* 2382 */    MCD::OPC_CheckPredicate, 12, 215, 43, // Skip to: 13609
/* 2386 */    MCD::OPC_CheckField, 6, 5, 0, 209, 43, // Skip to: 13609
/* 2392 */    MCD::OPC_Decode, 224, 3, 94, // Opcode: C_LE_S
/* 2396 */    MCD::OPC_FilterValue, 63, 201, 43, // Skip to: 13609
/* 2400 */    MCD::OPC_CheckPredicate, 12, 197, 43, // Skip to: 13609
/* 2404 */    MCD::OPC_CheckField, 6, 5, 0, 191, 43, // Skip to: 13609
/* 2410 */    MCD::OPC_Decode, 239, 3, 94, // Opcode: C_NGT_S
/* 2414 */    MCD::OPC_FilterValue, 17, 80, 2, // Skip to: 3010
/* 2418 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 2421 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 2433
/* 2425 */    MCD::OPC_CheckPredicate, 19, 172, 43, // Skip to: 13609
/* 2429 */    MCD::OPC_Decode, 152, 5, 95, // Opcode: FADD_D32
/* 2433 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 2445
/* 2437 */    MCD::OPC_CheckPredicate, 19, 160, 43, // Skip to: 13609
/* 2441 */    MCD::OPC_Decode, 154, 6, 95, // Opcode: FSUB_D32
/* 2445 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 2457
/* 2449 */    MCD::OPC_CheckPredicate, 19, 148, 43, // Skip to: 13609
/* 2453 */    MCD::OPC_Decode, 245, 5, 95, // Opcode: FMUL_D32
/* 2457 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 2469
/* 2461 */    MCD::OPC_CheckPredicate, 19, 136, 43, // Skip to: 13609
/* 2465 */    MCD::OPC_Decode, 188, 5, 95, // Opcode: FDIV_D32
/* 2469 */    MCD::OPC_FilterValue, 4, 14, 0, // Skip to: 2487
/* 2473 */    MCD::OPC_CheckPredicate, 21, 124, 43, // Skip to: 13609
/* 2477 */    MCD::OPC_CheckField, 16, 5, 0, 118, 43, // Skip to: 13609
/* 2483 */    MCD::OPC_Decode, 147, 6, 96, // Opcode: FSQRT_D32
/* 2487 */    MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 2505
/* 2491 */    MCD::OPC_CheckPredicate, 19, 106, 43, // Skip to: 13609
/* 2495 */    MCD::OPC_CheckField, 16, 5, 0, 100, 43, // Skip to: 13609
/* 2501 */    MCD::OPC_Decode, 145, 5, 96, // Opcode: FABS_D32
/* 2505 */    MCD::OPC_FilterValue, 6, 14, 0, // Skip to: 2523
/* 2509 */    MCD::OPC_CheckPredicate, 19, 88, 43, // Skip to: 13609
/* 2513 */    MCD::OPC_CheckField, 16, 5, 0, 82, 43, // Skip to: 13609
/* 2519 */    MCD::OPC_Decode, 237, 5, 96, // Opcode: FMOV_D32
/* 2523 */    MCD::OPC_FilterValue, 7, 14, 0, // Skip to: 2541
/* 2527 */    MCD::OPC_CheckPredicate, 19, 70, 43, // Skip to: 13609
/* 2531 */    MCD::OPC_CheckField, 16, 5, 0, 64, 43, // Skip to: 13609
/* 2537 */    MCD::OPC_Decode, 251, 5, 96, // Opcode: FNEG_D32
/* 2541 */    MCD::OPC_FilterValue, 12, 14, 0, // Skip to: 2559
/* 2545 */    MCD::OPC_CheckPredicate, 21, 52, 43, // Skip to: 13609
/* 2549 */    MCD::OPC_CheckField, 16, 5, 0, 46, 43, // Skip to: 13609
/* 2555 */    MCD::OPC_Decode, 228, 10, 97, // Opcode: ROUND_W_D32
/* 2559 */    MCD::OPC_FilterValue, 13, 14, 0, // Skip to: 2577
/* 2563 */    MCD::OPC_CheckPredicate, 21, 34, 43, // Skip to: 13609
/* 2567 */    MCD::OPC_CheckField, 16, 5, 0, 28, 43, // Skip to: 13609
/* 2573 */    MCD::OPC_Decode, 190, 13, 97, // Opcode: TRUNC_W_D32
/* 2577 */    MCD::OPC_FilterValue, 14, 14, 0, // Skip to: 2595
/* 2581 */    MCD::OPC_CheckPredicate, 21, 16, 43, // Skip to: 13609
/* 2585 */    MCD::OPC_CheckField, 16, 5, 0, 10, 43, // Skip to: 13609
/* 2591 */    MCD::OPC_Decode, 206, 2, 97, // Opcode: CEIL_W_D32
/* 2595 */    MCD::OPC_FilterValue, 15, 14, 0, // Skip to: 2613
/* 2599 */    MCD::OPC_CheckPredicate, 21, 254, 42, // Skip to: 13609
/* 2603 */    MCD::OPC_CheckField, 16, 5, 0, 248, 42, // Skip to: 13609
/* 2609 */    MCD::OPC_Decode, 222, 5, 97, // Opcode: FLOOR_W_D32
/* 2613 */    MCD::OPC_FilterValue, 17, 27, 0, // Skip to: 2644
/* 2617 */    MCD::OPC_ExtractField, 16, 2,  // Inst{17-16} ...
/* 2620 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 2632
/* 2624 */    MCD::OPC_CheckPredicate, 22, 229, 42, // Skip to: 13609
/* 2628 */    MCD::OPC_Decode, 211, 8, 98, // Opcode: MOVF_D32
/* 2632 */    MCD::OPC_FilterValue, 1, 221, 42, // Skip to: 13609
/* 2636 */    MCD::OPC_CheckPredicate, 22, 217, 42, // Skip to: 13609
/* 2640 */    MCD::OPC_Decode, 231, 8, 98, // Opcode: MOVT_D32
/* 2644 */    MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 2656
/* 2648 */    MCD::OPC_CheckPredicate, 22, 205, 42, // Skip to: 13609
/* 2652 */    MCD::OPC_Decode, 243, 8, 99, // Opcode: MOVZ_I_D32
/* 2656 */    MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 2668
/* 2660 */    MCD::OPC_CheckPredicate, 22, 193, 42, // Skip to: 13609
/* 2664 */    MCD::OPC_Decode, 223, 8, 99, // Opcode: MOVN_I_D32
/* 2668 */    MCD::OPC_FilterValue, 32, 14, 0, // Skip to: 2686
/* 2672 */    MCD::OPC_CheckPredicate, 19, 181, 42, // Skip to: 13609
/* 2676 */    MCD::OPC_CheckField, 16, 5, 0, 175, 42, // Skip to: 13609
/* 2682 */    MCD::OPC_Decode, 205, 3, 97, // Opcode: CVT_S_D32
/* 2686 */    MCD::OPC_FilterValue, 36, 14, 0, // Skip to: 2704
/* 2690 */    MCD::OPC_CheckPredicate, 19, 163, 42, // Skip to: 13609
/* 2694 */    MCD::OPC_CheckField, 16, 5, 0, 157, 42, // Skip to: 13609
/* 2700 */    MCD::OPC_Decode, 211, 3, 97, // Opcode: CVT_W_D32
/* 2704 */    MCD::OPC_FilterValue, 37, 14, 0, // Skip to: 2722
/* 2708 */    MCD::OPC_CheckPredicate, 20, 145, 42, // Skip to: 13609
/* 2712 */    MCD::OPC_CheckField, 16, 5, 0, 139, 42, // Skip to: 13609
/* 2718 */    MCD::OPC_Decode, 201, 3, 100, // Opcode: CVT_L_D64
/* 2722 */    MCD::OPC_FilterValue, 48, 14, 0, // Skip to: 2740
/* 2726 */    MCD::OPC_CheckPredicate, 23, 127, 42, // Skip to: 13609
/* 2730 */    MCD::OPC_CheckField, 6, 5, 0, 121, 42, // Skip to: 13609
/* 2736 */    MCD::OPC_Decode, 219, 3, 101, // Opcode: C_F_D32
/* 2740 */    MCD::OPC_FilterValue, 49, 14, 0, // Skip to: 2758
/* 2744 */    MCD::OPC_CheckPredicate, 23, 109, 42, // Skip to: 13609
/* 2748 */    MCD::OPC_CheckField, 6, 5, 0, 103, 42, // Skip to: 13609
/* 2754 */    MCD::OPC_Decode, 133, 4, 101, // Opcode: C_UN_D32
/* 2758 */    MCD::OPC_FilterValue, 50, 14, 0, // Skip to: 2776
/* 2762 */    MCD::OPC_CheckPredicate, 23, 91, 42, // Skip to: 13609
/* 2766 */    MCD::OPC_CheckField, 6, 5, 0, 85, 42, // Skip to: 13609
/* 2772 */    MCD::OPC_Decode, 216, 3, 101, // Opcode: C_EQ_D32
/* 2776 */    MCD::OPC_FilterValue, 51, 14, 0, // Skip to: 2794
/* 2780 */    MCD::OPC_CheckPredicate, 23, 73, 42, // Skip to: 13609
/* 2784 */    MCD::OPC_CheckField, 6, 5, 0, 67, 42, // Skip to: 13609
/* 2790 */    MCD::OPC_Decode, 252, 3, 101, // Opcode: C_UEQ_D32
/* 2794 */    MCD::OPC_FilterValue, 52, 14, 0, // Skip to: 2812
/* 2798 */    MCD::OPC_CheckPredicate, 23, 55, 42, // Skip to: 13609
/* 2802 */    MCD::OPC_CheckField, 6, 5, 0, 49, 42, // Skip to: 13609
/* 2808 */    MCD::OPC_Decode, 243, 3, 101, // Opcode: C_OLT_D32
/* 2812 */    MCD::OPC_FilterValue, 53, 14, 0, // Skip to: 2830
/* 2816 */    MCD::OPC_CheckPredicate, 23, 37, 42, // Skip to: 13609
/* 2820 */    MCD::OPC_CheckField, 6, 5, 0, 31, 42, // Skip to: 13609
/* 2826 */    MCD::OPC_Decode, 130, 4, 101, // Opcode: C_ULT_D32
/* 2830 */    MCD::OPC_FilterValue, 54, 14, 0, // Skip to: 2848
/* 2834 */    MCD::OPC_CheckPredicate, 23, 19, 42, // Skip to: 13609
/* 2838 */    MCD::OPC_CheckField, 6, 5, 0, 13, 42, // Skip to: 13609
/* 2844 */    MCD::OPC_Decode, 240, 3, 101, // Opcode: C_OLE_D32
/* 2848 */    MCD::OPC_FilterValue, 55, 14, 0, // Skip to: 2866
/* 2852 */    MCD::OPC_CheckPredicate, 23, 1, 42, // Skip to: 13609
/* 2856 */    MCD::OPC_CheckField, 6, 5, 0, 251, 41, // Skip to: 13609
/* 2862 */    MCD::OPC_Decode, 255, 3, 101, // Opcode: C_ULE_D32
/* 2866 */    MCD::OPC_FilterValue, 56, 14, 0, // Skip to: 2884
/* 2870 */    MCD::OPC_CheckPredicate, 23, 239, 41, // Skip to: 13609
/* 2874 */    MCD::OPC_CheckField, 6, 5, 0, 233, 41, // Skip to: 13609
/* 2880 */    MCD::OPC_Decode, 249, 3, 101, // Opcode: C_SF_D32
/* 2884 */    MCD::OPC_FilterValue, 57, 14, 0, // Skip to: 2902
/* 2888 */    MCD::OPC_CheckPredicate, 23, 221, 41, // Skip to: 13609
/* 2892 */    MCD::OPC_CheckField, 6, 5, 0, 215, 41, // Skip to: 13609
/* 2898 */    MCD::OPC_Decode, 231, 3, 101, // Opcode: C_NGLE_D32
/* 2902 */    MCD::OPC_FilterValue, 58, 14, 0, // Skip to: 2920
/* 2906 */    MCD::OPC_CheckPredicate, 23, 203, 41, // Skip to: 13609
/* 2910 */    MCD::OPC_CheckField, 6, 5, 0, 197, 41, // Skip to: 13609
/* 2916 */    MCD::OPC_Decode, 246, 3, 101, // Opcode: C_SEQ_D32
/* 2920 */    MCD::OPC_FilterValue, 59, 14, 0, // Skip to: 2938
/* 2924 */    MCD::OPC_CheckPredicate, 23, 185, 41, // Skip to: 13609
/* 2928 */    MCD::OPC_CheckField, 6, 5, 0, 179, 41, // Skip to: 13609
/* 2934 */    MCD::OPC_Decode, 234, 3, 101, // Opcode: C_NGL_D32
/* 2938 */    MCD::OPC_FilterValue, 60, 14, 0, // Skip to: 2956
/* 2942 */    MCD::OPC_CheckPredicate, 23, 167, 41, // Skip to: 13609
/* 2946 */    MCD::OPC_CheckField, 6, 5, 0, 161, 41, // Skip to: 13609
/* 2952 */    MCD::OPC_Decode, 225, 3, 101, // Opcode: C_LT_D32
/* 2956 */    MCD::OPC_FilterValue, 61, 14, 0, // Skip to: 2974
/* 2960 */    MCD::OPC_CheckPredicate, 23, 149, 41, // Skip to: 13609
/* 2964 */    MCD::OPC_CheckField, 6, 5, 0, 143, 41, // Skip to: 13609
/* 2970 */    MCD::OPC_Decode, 228, 3, 101, // Opcode: C_NGE_D32
/* 2974 */    MCD::OPC_FilterValue, 62, 14, 0, // Skip to: 2992
/* 2978 */    MCD::OPC_CheckPredicate, 23, 131, 41, // Skip to: 13609
/* 2982 */    MCD::OPC_CheckField, 6, 5, 0, 125, 41, // Skip to: 13609
/* 2988 */    MCD::OPC_Decode, 222, 3, 101, // Opcode: C_LE_D32
/* 2992 */    MCD::OPC_FilterValue, 63, 117, 41, // Skip to: 13609
/* 2996 */    MCD::OPC_CheckPredicate, 23, 113, 41, // Skip to: 13609
/* 3000 */    MCD::OPC_CheckField, 6, 5, 0, 107, 41, // Skip to: 13609
/* 3006 */    MCD::OPC_Decode, 237, 3, 101, // Opcode: C_NGT_D32
/* 3010 */    MCD::OPC_FilterValue, 20, 39, 0, // Skip to: 3053
/* 3014 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 3017 */    MCD::OPC_FilterValue, 32, 14, 0, // Skip to: 3035
/* 3021 */    MCD::OPC_CheckPredicate, 1, 88, 41, // Skip to: 13609
/* 3025 */    MCD::OPC_CheckField, 16, 5, 0, 82, 41, // Skip to: 13609
/* 3031 */    MCD::OPC_Decode, 209, 3, 89, // Opcode: CVT_S_W
/* 3035 */    MCD::OPC_FilterValue, 33, 74, 41, // Skip to: 13609
/* 3039 */    MCD::OPC_CheckPredicate, 19, 70, 41, // Skip to: 13609
/* 3043 */    MCD::OPC_CheckField, 16, 5, 0, 64, 41, // Skip to: 13609
/* 3049 */    MCD::OPC_Decode, 195, 3, 92, // Opcode: CVT_D32_W
/* 3053 */    MCD::OPC_FilterValue, 24, 8, 0, // Skip to: 3065
/* 3057 */    MCD::OPC_CheckPredicate, 7, 52, 41, // Skip to: 13609
/* 3061 */    MCD::OPC_Decode, 171, 2, 87, // Opcode: BZ_B
/* 3065 */    MCD::OPC_FilterValue, 25, 8, 0, // Skip to: 3077
/* 3069 */    MCD::OPC_CheckPredicate, 7, 40, 41, // Skip to: 13609
/* 3073 */    MCD::OPC_Decode, 173, 2, 102, // Opcode: BZ_H
/* 3077 */    MCD::OPC_FilterValue, 26, 8, 0, // Skip to: 3089
/* 3081 */    MCD::OPC_CheckPredicate, 7, 28, 41, // Skip to: 13609
/* 3085 */    MCD::OPC_Decode, 175, 2, 103, // Opcode: BZ_W
/* 3089 */    MCD::OPC_FilterValue, 27, 8, 0, // Skip to: 3101
/* 3093 */    MCD::OPC_CheckPredicate, 7, 16, 41, // Skip to: 13609
/* 3097 */    MCD::OPC_Decode, 172, 2, 104, // Opcode: BZ_D
/* 3101 */    MCD::OPC_FilterValue, 28, 8, 0, // Skip to: 3113
/* 3105 */    MCD::OPC_CheckPredicate, 7, 4, 41, // Skip to: 13609
/* 3109 */    MCD::OPC_Decode, 145, 2, 87, // Opcode: BNZ_B
/* 3113 */    MCD::OPC_FilterValue, 29, 8, 0, // Skip to: 3125
/* 3117 */    MCD::OPC_CheckPredicate, 7, 248, 40, // Skip to: 13609
/* 3121 */    MCD::OPC_Decode, 147, 2, 102, // Opcode: BNZ_H
/* 3125 */    MCD::OPC_FilterValue, 30, 8, 0, // Skip to: 3137
/* 3129 */    MCD::OPC_CheckPredicate, 7, 236, 40, // Skip to: 13609
/* 3133 */    MCD::OPC_Decode, 149, 2, 103, // Opcode: BNZ_W
/* 3137 */    MCD::OPC_FilterValue, 31, 228, 40, // Skip to: 13609
/* 3141 */    MCD::OPC_CheckPredicate, 7, 224, 40, // Skip to: 13609
/* 3145 */    MCD::OPC_Decode, 146, 2, 104, // Opcode: BNZ_D
/* 3149 */    MCD::OPC_FilterValue, 18, 39, 0, // Skip to: 3192
/* 3153 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 3156 */    MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 3174
/* 3160 */    MCD::OPC_CheckPredicate, 1, 205, 40, // Skip to: 13609
/* 3164 */    MCD::OPC_CheckField, 3, 8, 0, 199, 40, // Skip to: 13609
/* 3170 */    MCD::OPC_Decode, 158, 8, 77, // Opcode: MFC2
/* 3174 */    MCD::OPC_FilterValue, 4, 191, 40, // Skip to: 13609
/* 3178 */    MCD::OPC_CheckPredicate, 1, 187, 40, // Skip to: 13609
/* 3182 */    MCD::OPC_CheckField, 3, 8, 0, 181, 40, // Skip to: 13609
/* 3188 */    MCD::OPC_Decode, 147, 9, 77, // Opcode: MTC2
/* 3192 */    MCD::OPC_FilterValue, 19, 207, 0, // Skip to: 3403
/* 3196 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 3199 */    MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 3217
/* 3203 */    MCD::OPC_CheckPredicate, 24, 162, 40, // Skip to: 13609
/* 3207 */    MCD::OPC_CheckField, 11, 5, 0, 156, 40, // Skip to: 13609
/* 3213 */    MCD::OPC_Decode, 213, 7, 105, // Opcode: LWXC1
/* 3217 */    MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 3235
/* 3221 */    MCD::OPC_CheckPredicate, 25, 144, 40, // Skip to: 13609
/* 3225 */    MCD::OPC_CheckField, 11, 5, 0, 138, 40, // Skip to: 13609
/* 3231 */    MCD::OPC_Decode, 153, 7, 106, // Opcode: LDXC1
/* 3235 */    MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 3253
/* 3239 */    MCD::OPC_CheckPredicate, 26, 126, 40, // Skip to: 13609
/* 3243 */    MCD::OPC_CheckField, 11, 5, 0, 120, 40, // Skip to: 13609
/* 3249 */    MCD::OPC_Decode, 185, 7, 106, // Opcode: LUXC1
/* 3253 */    MCD::OPC_FilterValue, 8, 14, 0, // Skip to: 3271
/* 3257 */    MCD::OPC_CheckPredicate, 24, 108, 40, // Skip to: 13609
/* 3261 */    MCD::OPC_CheckField, 6, 5, 0, 102, 40, // Skip to: 13609
/* 3267 */    MCD::OPC_Decode, 228, 12, 107, // Opcode: SWXC1
/* 3271 */    MCD::OPC_FilterValue, 9, 14, 0, // Skip to: 3289
/* 3275 */    MCD::OPC_CheckPredicate, 25, 90, 40, // Skip to: 13609
/* 3279 */    MCD::OPC_CheckField, 6, 5, 0, 84, 40, // Skip to: 13609
/* 3285 */    MCD::OPC_Decode, 141, 11, 108, // Opcode: SDXC1
/* 3289 */    MCD::OPC_FilterValue, 13, 14, 0, // Skip to: 3307
/* 3293 */    MCD::OPC_CheckPredicate, 26, 72, 40, // Skip to: 13609
/* 3297 */    MCD::OPC_CheckField, 6, 5, 0, 66, 40, // Skip to: 13609
/* 3303 */    MCD::OPC_Decode, 207, 12, 108, // Opcode: SUXC1
/* 3307 */    MCD::OPC_FilterValue, 32, 8, 0, // Skip to: 3319
/* 3311 */    MCD::OPC_CheckPredicate, 27, 54, 40, // Skip to: 13609
/* 3315 */    MCD::OPC_Decode, 253, 7, 109, // Opcode: MADD_S
/* 3319 */    MCD::OPC_FilterValue, 33, 8, 0, // Skip to: 3331
/* 3323 */    MCD::OPC_CheckPredicate, 28, 42, 40, // Skip to: 13609
/* 3327 */    MCD::OPC_Decode, 246, 7, 110, // Opcode: MADD_D32
/* 3331 */    MCD::OPC_FilterValue, 40, 8, 0, // Skip to: 3343
/* 3335 */    MCD::OPC_CheckPredicate, 27, 30, 40, // Skip to: 13609
/* 3339 */    MCD::OPC_Decode, 142, 9, 109, // Opcode: MSUB_S
/* 3343 */    MCD::OPC_FilterValue, 41, 8, 0, // Skip to: 3355
/* 3347 */    MCD::OPC_CheckPredicate, 28, 18, 40, // Skip to: 13609
/* 3351 */    MCD::OPC_Decode, 135, 9, 110, // Opcode: MSUB_D32
/* 3355 */    MCD::OPC_FilterValue, 48, 8, 0, // Skip to: 3367
/* 3359 */    MCD::OPC_CheckPredicate, 27, 6, 40, // Skip to: 13609
/* 3363 */    MCD::OPC_Decode, 217, 9, 109, // Opcode: NMADD_S
/* 3367 */    MCD::OPC_FilterValue, 49, 8, 0, // Skip to: 3379
/* 3371 */    MCD::OPC_CheckPredicate, 28, 250, 39, // Skip to: 13609
/* 3375 */    MCD::OPC_Decode, 214, 9, 110, // Opcode: NMADD_D32
/* 3379 */    MCD::OPC_FilterValue, 56, 8, 0, // Skip to: 3391
/* 3383 */    MCD::OPC_CheckPredicate, 27, 238, 39, // Skip to: 13609
/* 3387 */    MCD::OPC_Decode, 222, 9, 109, // Opcode: NMSUB_S
/* 3391 */    MCD::OPC_FilterValue, 57, 230, 39, // Skip to: 13609
/* 3395 */    MCD::OPC_CheckPredicate, 28, 226, 39, // Skip to: 13609
/* 3399 */    MCD::OPC_Decode, 219, 9, 110, // Opcode: NMSUB_D32
/* 3403 */    MCD::OPC_FilterValue, 20, 8, 0, // Skip to: 3415
/* 3407 */    MCD::OPC_CheckPredicate, 14, 214, 39, // Skip to: 13609
/* 3411 */    MCD::OPC_Decode, 191, 1, 74, // Opcode: BEQL
/* 3415 */    MCD::OPC_FilterValue, 21, 8, 0, // Skip to: 3427
/* 3419 */    MCD::OPC_CheckPredicate, 14, 202, 39, // Skip to: 13609
/* 3423 */    MCD::OPC_Decode, 138, 2, 74, // Opcode: BNEL
/* 3427 */    MCD::OPC_FilterValue, 22, 14, 0, // Skip to: 3445
/* 3431 */    MCD::OPC_CheckPredicate, 14, 190, 39, // Skip to: 13609
/* 3435 */    MCD::OPC_CheckField, 16, 5, 0, 184, 39, // Skip to: 13609
/* 3441 */    MCD::OPC_Decode, 237, 1, 69, // Opcode: BLEZL
/* 3445 */    MCD::OPC_FilterValue, 23, 14, 0, // Skip to: 3463
/* 3449 */    MCD::OPC_CheckPredicate, 14, 172, 39, // Skip to: 13609
/* 3453 */    MCD::OPC_CheckField, 16, 5, 0, 166, 39, // Skip to: 13609
/* 3459 */    MCD::OPC_Decode, 213, 1, 69, // Opcode: BGTZL
/* 3463 */    MCD::OPC_FilterValue, 28, 229, 0, // Skip to: 3696
/* 3467 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 3470 */    MCD::OPC_FilterValue, 0, 36, 0, // Skip to: 3510
/* 3474 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3477 */    MCD::OPC_FilterValue, 0, 144, 39, // Skip to: 13609
/* 3481 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 3484 */    MCD::OPC_FilterValue, 0, 137, 39, // Skip to: 13609
/* 3488 */    MCD::OPC_CheckPredicate, 8, 10, 0, // Skip to: 3502
/* 3492 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 3502
/* 3498 */    MCD::OPC_Decode, 234, 7, 40, // Opcode: MADD
/* 3502 */    MCD::OPC_CheckPredicate, 11, 119, 39, // Skip to: 13609
/* 3506 */    MCD::OPC_Decode, 249, 7, 111, // Opcode: MADD_DSP
/* 3510 */    MCD::OPC_FilterValue, 1, 36, 0, // Skip to: 3550
/* 3514 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3517 */    MCD::OPC_FilterValue, 0, 104, 39, // Skip to: 13609
/* 3521 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 3524 */    MCD::OPC_FilterValue, 0, 97, 39, // Skip to: 13609
/* 3528 */    MCD::OPC_CheckPredicate, 8, 10, 0, // Skip to: 3542
/* 3532 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 3542
/* 3538 */    MCD::OPC_Decode, 239, 7, 40, // Opcode: MADDU
/* 3542 */    MCD::OPC_CheckPredicate, 11, 79, 39, // Skip to: 13609
/* 3546 */    MCD::OPC_Decode, 240, 7, 111, // Opcode: MADDU_DSP
/* 3550 */    MCD::OPC_FilterValue, 2, 14, 0, // Skip to: 3568
/* 3554 */    MCD::OPC_CheckPredicate, 8, 67, 39, // Skip to: 13609
/* 3558 */    MCD::OPC_CheckField, 6, 5, 0, 61, 39, // Skip to: 13609
/* 3564 */    MCD::OPC_Decode, 168, 9, 32, // Opcode: MUL
/* 3568 */    MCD::OPC_FilterValue, 4, 36, 0, // Skip to: 3608
/* 3572 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3575 */    MCD::OPC_FilterValue, 0, 46, 39, // Skip to: 13609
/* 3579 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 3582 */    MCD::OPC_FilterValue, 0, 39, 39, // Skip to: 13609
/* 3586 */    MCD::OPC_CheckPredicate, 8, 10, 0, // Skip to: 3600
/* 3590 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 3600
/* 3596 */    MCD::OPC_Decode, 251, 8, 40, // Opcode: MSUB
/* 3600 */    MCD::OPC_CheckPredicate, 11, 21, 39, // Skip to: 13609
/* 3604 */    MCD::OPC_Decode, 138, 9, 111, // Opcode: MSUB_DSP
/* 3608 */    MCD::OPC_FilterValue, 5, 36, 0, // Skip to: 3648
/* 3612 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 3615 */    MCD::OPC_FilterValue, 0, 6, 39, // Skip to: 13609
/* 3619 */    MCD::OPC_ExtractField, 13, 3,  // Inst{15-13} ...
/* 3622 */    MCD::OPC_FilterValue, 0, 255, 38, // Skip to: 13609
/* 3626 */    MCD::OPC_CheckPredicate, 8, 10, 0, // Skip to: 3640
/* 3630 */    MCD::OPC_CheckField, 11, 2, 0, 4, 0, // Skip to: 3640
/* 3636 */    MCD::OPC_Decode, 128, 9, 40, // Opcode: MSUBU
/* 3640 */    MCD::OPC_CheckPredicate, 11, 237, 38, // Skip to: 13609
/* 3644 */    MCD::OPC_Decode, 129, 9, 111, // Opcode: MSUBU_DSP
/* 3648 */    MCD::OPC_FilterValue, 32, 14, 0, // Skip to: 3666
/* 3652 */    MCD::OPC_CheckPredicate, 8, 225, 38, // Skip to: 13609
/* 3656 */    MCD::OPC_CheckField, 6, 5, 0, 219, 38, // Skip to: 13609
/* 3662 */    MCD::OPC_Decode, 133, 3, 112, // Opcode: CLZ
/* 3666 */    MCD::OPC_FilterValue, 33, 14, 0, // Skip to: 3684
/* 3670 */    MCD::OPC_CheckPredicate, 8, 207, 38, // Skip to: 13609
/* 3674 */    MCD::OPC_CheckField, 6, 5, 0, 201, 38, // Skip to: 13609
/* 3680 */    MCD::OPC_Decode, 242, 2, 112, // Opcode: CLO
/* 3684 */    MCD::OPC_FilterValue, 63, 193, 38, // Skip to: 13609
/* 3688 */    MCD::OPC_CheckPredicate, 8, 189, 38, // Skip to: 13609
/* 3692 */    MCD::OPC_Decode, 255, 10, 60, // Opcode: SDBBP
/* 3696 */    MCD::OPC_FilterValue, 29, 8, 0, // Skip to: 3708
/* 3700 */    MCD::OPC_CheckPredicate, 8, 177, 38, // Skip to: 13609
/* 3704 */    MCD::OPC_Decode, 240, 6, 73, // Opcode: JALX
/* 3708 */    MCD::OPC_FilterValue, 30, 252, 27, // Skip to: 10876
/* 3712 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 3715 */    MCD::OPC_FilterValue, 0, 50, 0, // Skip to: 3769
/* 3719 */    MCD::OPC_ExtractField, 24, 2,  // Inst{25-24} ...
/* 3722 */    MCD::OPC_FilterValue, 0, 7, 0, // Skip to: 3733
/* 3726 */    MCD::OPC_CheckPredicate, 7, 151, 38, // Skip to: 13609
/* 3730 */    MCD::OPC_Decode, 86, 113, // Opcode: ANDI_B
/* 3733 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 3745
/* 3737 */    MCD::OPC_CheckPredicate, 7, 140, 38, // Skip to: 13609
/* 3741 */    MCD::OPC_Decode, 239, 9, 113, // Opcode: ORI_B
/* 3745 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 3757
/* 3749 */    MCD::OPC_CheckPredicate, 7, 128, 38, // Skip to: 13609
/* 3753 */    MCD::OPC_Decode, 227, 9, 113, // Opcode: NORI_B
/* 3757 */    MCD::OPC_FilterValue, 3, 120, 38, // Skip to: 13609
/* 3761 */    MCD::OPC_CheckPredicate, 7, 116, 38, // Skip to: 13609
/* 3765 */    MCD::OPC_Decode, 213, 13, 113, // Opcode: XORI_B
/* 3769 */    MCD::OPC_FilterValue, 1, 39, 0, // Skip to: 3812
/* 3773 */    MCD::OPC_ExtractField, 24, 2,  // Inst{25-24} ...
/* 3776 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 3788
/* 3780 */    MCD::OPC_CheckPredicate, 7, 97, 38, // Skip to: 13609
/* 3784 */    MCD::OPC_Decode, 251, 1, 114, // Opcode: BMNZI_B
/* 3788 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 3800
/* 3792 */    MCD::OPC_CheckPredicate, 7, 85, 38, // Skip to: 13609
/* 3796 */    MCD::OPC_Decode, 253, 1, 114, // Opcode: BMZI_B
/* 3800 */    MCD::OPC_FilterValue, 2, 77, 38, // Skip to: 13609
/* 3804 */    MCD::OPC_CheckPredicate, 7, 73, 38, // Skip to: 13609
/* 3808 */    MCD::OPC_Decode, 156, 2, 114, // Opcode: BSELI_B
/* 3812 */    MCD::OPC_FilterValue, 2, 39, 0, // Skip to: 3855
/* 3816 */    MCD::OPC_ExtractField, 24, 2,  // Inst{25-24} ...
/* 3819 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 3831
/* 3823 */    MCD::OPC_CheckPredicate, 7, 54, 38, // Skip to: 13609
/* 3827 */    MCD::OPC_Decode, 164, 11, 113, // Opcode: SHF_B
/* 3831 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 3843
/* 3835 */    MCD::OPC_CheckPredicate, 7, 42, 38, // Skip to: 13609
/* 3839 */    MCD::OPC_Decode, 165, 11, 115, // Opcode: SHF_H
/* 3843 */    MCD::OPC_FilterValue, 2, 34, 38, // Skip to: 13609
/* 3847 */    MCD::OPC_CheckPredicate, 7, 30, 38, // Skip to: 13609
/* 3851 */    MCD::OPC_Decode, 166, 11, 116, // Opcode: SHF_W
/* 3855 */    MCD::OPC_FilterValue, 6, 31, 1, // Skip to: 4146
/* 3859 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 3862 */    MCD::OPC_FilterValue, 0, 7, 0, // Skip to: 3873
/* 3866 */    MCD::OPC_CheckPredicate, 7, 11, 38, // Skip to: 13609
/* 3870 */    MCD::OPC_Decode, 58, 117, // Opcode: ADDVI_B
/* 3873 */    MCD::OPC_FilterValue, 1, 7, 0, // Skip to: 3884
/* 3877 */    MCD::OPC_CheckPredicate, 7, 0, 38, // Skip to: 13609
/* 3881 */    MCD::OPC_Decode, 60, 118, // Opcode: ADDVI_H
/* 3884 */    MCD::OPC_FilterValue, 2, 7, 0, // Skip to: 3895
/* 3888 */    MCD::OPC_CheckPredicate, 7, 245, 37, // Skip to: 13609
/* 3892 */    MCD::OPC_Decode, 61, 119, // Opcode: ADDVI_W
/* 3895 */    MCD::OPC_FilterValue, 3, 7, 0, // Skip to: 3906
/* 3899 */    MCD::OPC_CheckPredicate, 7, 234, 37, // Skip to: 13609
/* 3903 */    MCD::OPC_Decode, 59, 120, // Opcode: ADDVI_D
/* 3906 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 3918
/* 3910 */    MCD::OPC_CheckPredicate, 7, 223, 37, // Skip to: 13609
/* 3914 */    MCD::OPC_Decode, 196, 12, 117, // Opcode: SUBVI_B
/* 3918 */    MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 3930
/* 3922 */    MCD::OPC_CheckPredicate, 7, 211, 37, // Skip to: 13609
/* 3926 */    MCD::OPC_Decode, 198, 12, 118, // Opcode: SUBVI_H
/* 3930 */    MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 3942
/* 3934 */    MCD::OPC_CheckPredicate, 7, 199, 37, // Skip to: 13609
/* 3938 */    MCD::OPC_Decode, 199, 12, 119, // Opcode: SUBVI_W
/* 3942 */    MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 3954
/* 3946 */    MCD::OPC_CheckPredicate, 7, 187, 37, // Skip to: 13609
/* 3950 */    MCD::OPC_Decode, 197, 12, 120, // Opcode: SUBVI_D
/* 3954 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 3966
/* 3958 */    MCD::OPC_CheckPredicate, 7, 175, 37, // Skip to: 13609
/* 3962 */    MCD::OPC_Decode, 133, 8, 117, // Opcode: MAXI_S_B
/* 3966 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 3978
/* 3970 */    MCD::OPC_CheckPredicate, 7, 163, 37, // Skip to: 13609
/* 3974 */    MCD::OPC_Decode, 135, 8, 118, // Opcode: MAXI_S_H
/* 3978 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 3990
/* 3982 */    MCD::OPC_CheckPredicate, 7, 151, 37, // Skip to: 13609
/* 3986 */    MCD::OPC_Decode, 136, 8, 119, // Opcode: MAXI_S_W
/* 3990 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 4002
/* 3994 */    MCD::OPC_CheckPredicate, 7, 139, 37, // Skip to: 13609
/* 3998 */    MCD::OPC_Decode, 134, 8, 120, // Opcode: MAXI_S_D
/* 4002 */    MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 4014
/* 4006 */    MCD::OPC_CheckPredicate, 7, 127, 37, // Skip to: 13609
/* 4010 */    MCD::OPC_Decode, 137, 8, 117, // Opcode: MAXI_U_B
/* 4014 */    MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 4026
/* 4018 */    MCD::OPC_CheckPredicate, 7, 115, 37, // Skip to: 13609
/* 4022 */    MCD::OPC_Decode, 139, 8, 118, // Opcode: MAXI_U_H
/* 4026 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 4038
/* 4030 */    MCD::OPC_CheckPredicate, 7, 103, 37, // Skip to: 13609
/* 4034 */    MCD::OPC_Decode, 140, 8, 119, // Opcode: MAXI_U_W
/* 4038 */    MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 4050
/* 4042 */    MCD::OPC_CheckPredicate, 7, 91, 37, // Skip to: 13609
/* 4046 */    MCD::OPC_Decode, 138, 8, 120, // Opcode: MAXI_U_D
/* 4050 */    MCD::OPC_FilterValue, 16, 8, 0, // Skip to: 4062
/* 4054 */    MCD::OPC_CheckPredicate, 7, 79, 37, // Skip to: 13609
/* 4058 */    MCD::OPC_Decode, 174, 8, 117, // Opcode: MINI_S_B
/* 4062 */    MCD::OPC_FilterValue, 17, 8, 0, // Skip to: 4074
/* 4066 */    MCD::OPC_CheckPredicate, 7, 67, 37, // Skip to: 13609
/* 4070 */    MCD::OPC_Decode, 176, 8, 118, // Opcode: MINI_S_H
/* 4074 */    MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 4086
/* 4078 */    MCD::OPC_CheckPredicate, 7, 55, 37, // Skip to: 13609
/* 4082 */    MCD::OPC_Decode, 177, 8, 119, // Opcode: MINI_S_W
/* 4086 */    MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 4098
/* 4090 */    MCD::OPC_CheckPredicate, 7, 43, 37, // Skip to: 13609
/* 4094 */    MCD::OPC_Decode, 175, 8, 120, // Opcode: MINI_S_D
/* 4098 */    MCD::OPC_FilterValue, 20, 8, 0, // Skip to: 4110
/* 4102 */    MCD::OPC_CheckPredicate, 7, 31, 37, // Skip to: 13609
/* 4106 */    MCD::OPC_Decode, 178, 8, 117, // Opcode: MINI_U_B
/* 4110 */    MCD::OPC_FilterValue, 21, 8, 0, // Skip to: 4122
/* 4114 */    MCD::OPC_CheckPredicate, 7, 19, 37, // Skip to: 13609
/* 4118 */    MCD::OPC_Decode, 180, 8, 118, // Opcode: MINI_U_H
/* 4122 */    MCD::OPC_FilterValue, 22, 8, 0, // Skip to: 4134
/* 4126 */    MCD::OPC_CheckPredicate, 7, 7, 37, // Skip to: 13609
/* 4130 */    MCD::OPC_Decode, 181, 8, 119, // Opcode: MINI_U_W
/* 4134 */    MCD::OPC_FilterValue, 23, 255, 36, // Skip to: 13609
/* 4138 */    MCD::OPC_CheckPredicate, 7, 251, 36, // Skip to: 13609
/* 4142 */    MCD::OPC_Decode, 179, 8, 120, // Opcode: MINI_U_D
/* 4146 */    MCD::OPC_FilterValue, 7, 35, 1, // Skip to: 4441
/* 4150 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 4153 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4165
/* 4157 */    MCD::OPC_CheckPredicate, 7, 232, 36, // Skip to: 13609
/* 4161 */    MCD::OPC_Decode, 211, 2, 117, // Opcode: CEQI_B
/* 4165 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 4177
/* 4169 */    MCD::OPC_CheckPredicate, 7, 220, 36, // Skip to: 13609
/* 4173 */    MCD::OPC_Decode, 213, 2, 118, // Opcode: CEQI_H
/* 4177 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 4189
/* 4181 */    MCD::OPC_CheckPredicate, 7, 208, 36, // Skip to: 13609
/* 4185 */    MCD::OPC_Decode, 214, 2, 119, // Opcode: CEQI_W
/* 4189 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 4201
/* 4193 */    MCD::OPC_CheckPredicate, 7, 196, 36, // Skip to: 13609
/* 4197 */    MCD::OPC_Decode, 212, 2, 120, // Opcode: CEQI_D
/* 4201 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 4213
/* 4205 */    MCD::OPC_CheckPredicate, 7, 184, 36, // Skip to: 13609
/* 4209 */    MCD::OPC_Decode, 245, 2, 117, // Opcode: CLTI_S_B
/* 4213 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 4225
/* 4217 */    MCD::OPC_CheckPredicate, 7, 172, 36, // Skip to: 13609
/* 4221 */    MCD::OPC_Decode, 247, 2, 118, // Opcode: CLTI_S_H
/* 4225 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 4237
/* 4229 */    MCD::OPC_CheckPredicate, 7, 160, 36, // Skip to: 13609
/* 4233 */    MCD::OPC_Decode, 248, 2, 119, // Opcode: CLTI_S_W
/* 4237 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 4249
/* 4241 */    MCD::OPC_CheckPredicate, 7, 148, 36, // Skip to: 13609
/* 4245 */    MCD::OPC_Decode, 246, 2, 120, // Opcode: CLTI_S_D
/* 4249 */    MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 4261
/* 4253 */    MCD::OPC_CheckPredicate, 7, 136, 36, // Skip to: 13609
/* 4257 */    MCD::OPC_Decode, 249, 2, 117, // Opcode: CLTI_U_B
/* 4261 */    MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 4273
/* 4265 */    MCD::OPC_CheckPredicate, 7, 124, 36, // Skip to: 13609
/* 4269 */    MCD::OPC_Decode, 251, 2, 118, // Opcode: CLTI_U_H
/* 4273 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 4285
/* 4277 */    MCD::OPC_CheckPredicate, 7, 112, 36, // Skip to: 13609
/* 4281 */    MCD::OPC_Decode, 252, 2, 119, // Opcode: CLTI_U_W
/* 4285 */    MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 4297
/* 4289 */    MCD::OPC_CheckPredicate, 7, 100, 36, // Skip to: 13609
/* 4293 */    MCD::OPC_Decode, 250, 2, 120, // Opcode: CLTI_U_D
/* 4297 */    MCD::OPC_FilterValue, 16, 8, 0, // Skip to: 4309
/* 4301 */    MCD::OPC_CheckPredicate, 7, 88, 36, // Skip to: 13609
/* 4305 */    MCD::OPC_Decode, 226, 2, 117, // Opcode: CLEI_S_B
/* 4309 */    MCD::OPC_FilterValue, 17, 8, 0, // Skip to: 4321
/* 4313 */    MCD::OPC_CheckPredicate, 7, 76, 36, // Skip to: 13609
/* 4317 */    MCD::OPC_Decode, 228, 2, 118, // Opcode: CLEI_S_H
/* 4321 */    MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 4333
/* 4325 */    MCD::OPC_CheckPredicate, 7, 64, 36, // Skip to: 13609
/* 4329 */    MCD::OPC_Decode, 229, 2, 119, // Opcode: CLEI_S_W
/* 4333 */    MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 4345
/* 4337 */    MCD::OPC_CheckPredicate, 7, 52, 36, // Skip to: 13609
/* 4341 */    MCD::OPC_Decode, 227, 2, 120, // Opcode: CLEI_S_D
/* 4345 */    MCD::OPC_FilterValue, 20, 8, 0, // Skip to: 4357
/* 4349 */    MCD::OPC_CheckPredicate, 7, 40, 36, // Skip to: 13609
/* 4353 */    MCD::OPC_Decode, 230, 2, 117, // Opcode: CLEI_U_B
/* 4357 */    MCD::OPC_FilterValue, 21, 8, 0, // Skip to: 4369
/* 4361 */    MCD::OPC_CheckPredicate, 7, 28, 36, // Skip to: 13609
/* 4365 */    MCD::OPC_Decode, 232, 2, 118, // Opcode: CLEI_U_H
/* 4369 */    MCD::OPC_FilterValue, 22, 8, 0, // Skip to: 4381
/* 4373 */    MCD::OPC_CheckPredicate, 7, 16, 36, // Skip to: 13609
/* 4377 */    MCD::OPC_Decode, 233, 2, 119, // Opcode: CLEI_U_W
/* 4381 */    MCD::OPC_FilterValue, 23, 8, 0, // Skip to: 4393
/* 4385 */    MCD::OPC_CheckPredicate, 7, 4, 36, // Skip to: 13609
/* 4389 */    MCD::OPC_Decode, 231, 2, 120, // Opcode: CLEI_U_D
/* 4393 */    MCD::OPC_FilterValue, 24, 8, 0, // Skip to: 4405
/* 4397 */    MCD::OPC_CheckPredicate, 7, 248, 35, // Skip to: 13609
/* 4401 */    MCD::OPC_Decode, 146, 7, 121, // Opcode: LDI_B
/* 4405 */    MCD::OPC_FilterValue, 25, 8, 0, // Skip to: 4417
/* 4409 */    MCD::OPC_CheckPredicate, 7, 236, 35, // Skip to: 13609
/* 4413 */    MCD::OPC_Decode, 148, 7, 122, // Opcode: LDI_H
/* 4417 */    MCD::OPC_FilterValue, 26, 8, 0, // Skip to: 4429
/* 4421 */    MCD::OPC_CheckPredicate, 7, 224, 35, // Skip to: 13609
/* 4425 */    MCD::OPC_Decode, 149, 7, 123, // Opcode: LDI_W
/* 4429 */    MCD::OPC_FilterValue, 27, 216, 35, // Skip to: 13609
/* 4433 */    MCD::OPC_CheckPredicate, 7, 212, 35, // Skip to: 13609
/* 4437 */    MCD::OPC_Decode, 147, 7, 124, // Opcode: LDI_D
/* 4441 */    MCD::OPC_FilterValue, 9, 43, 2, // Skip to: 5000
/* 4445 */    MCD::OPC_ExtractField, 22, 4,  // Inst{25-22} ...
/* 4448 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4460
/* 4452 */    MCD::OPC_CheckPredicate, 7, 193, 35, // Skip to: 13609
/* 4456 */    MCD::OPC_Decode, 205, 11, 125, // Opcode: SLLI_D
/* 4460 */    MCD::OPC_FilterValue, 1, 52, 0, // Skip to: 4516
/* 4464 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4467 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4479
/* 4471 */    MCD::OPC_CheckPredicate, 7, 174, 35, // Skip to: 13609
/* 4475 */    MCD::OPC_Decode, 207, 11, 119, // Opcode: SLLI_W
/* 4479 */    MCD::OPC_FilterValue, 1, 166, 35, // Skip to: 13609
/* 4483 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4486 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4498
/* 4490 */    MCD::OPC_CheckPredicate, 7, 155, 35, // Skip to: 13609
/* 4494 */    MCD::OPC_Decode, 206, 11, 126, // Opcode: SLLI_H
/* 4498 */    MCD::OPC_FilterValue, 1, 147, 35, // Skip to: 13609
/* 4502 */    MCD::OPC_CheckPredicate, 7, 143, 35, // Skip to: 13609
/* 4506 */    MCD::OPC_CheckField, 19, 1, 0, 137, 35, // Skip to: 13609
/* 4512 */    MCD::OPC_Decode, 204, 11, 127, // Opcode: SLLI_B
/* 4516 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 4528
/* 4520 */    MCD::OPC_CheckPredicate, 7, 125, 35, // Skip to: 13609
/* 4524 */    MCD::OPC_Decode, 244, 11, 125, // Opcode: SRAI_D
/* 4528 */    MCD::OPC_FilterValue, 3, 52, 0, // Skip to: 4584
/* 4532 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4535 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4547
/* 4539 */    MCD::OPC_CheckPredicate, 7, 106, 35, // Skip to: 13609
/* 4543 */    MCD::OPC_Decode, 246, 11, 119, // Opcode: SRAI_W
/* 4547 */    MCD::OPC_FilterValue, 1, 98, 35, // Skip to: 13609
/* 4551 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4554 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4566
/* 4558 */    MCD::OPC_CheckPredicate, 7, 87, 35, // Skip to: 13609
/* 4562 */    MCD::OPC_Decode, 245, 11, 126, // Opcode: SRAI_H
/* 4566 */    MCD::OPC_FilterValue, 1, 79, 35, // Skip to: 13609
/* 4570 */    MCD::OPC_CheckPredicate, 7, 75, 35, // Skip to: 13609
/* 4574 */    MCD::OPC_CheckField, 19, 1, 0, 69, 35, // Skip to: 13609
/* 4580 */    MCD::OPC_Decode, 243, 11, 127, // Opcode: SRAI_B
/* 4584 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 4596
/* 4588 */    MCD::OPC_CheckPredicate, 7, 57, 35, // Skip to: 13609
/* 4592 */    MCD::OPC_Decode, 137, 12, 125, // Opcode: SRLI_D
/* 4596 */    MCD::OPC_FilterValue, 5, 52, 0, // Skip to: 4652
/* 4600 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4603 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4615
/* 4607 */    MCD::OPC_CheckPredicate, 7, 38, 35, // Skip to: 13609
/* 4611 */    MCD::OPC_Decode, 139, 12, 119, // Opcode: SRLI_W
/* 4615 */    MCD::OPC_FilterValue, 1, 30, 35, // Skip to: 13609
/* 4619 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4622 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4634
/* 4626 */    MCD::OPC_CheckPredicate, 7, 19, 35, // Skip to: 13609
/* 4630 */    MCD::OPC_Decode, 138, 12, 126, // Opcode: SRLI_H
/* 4634 */    MCD::OPC_FilterValue, 1, 11, 35, // Skip to: 13609
/* 4638 */    MCD::OPC_CheckPredicate, 7, 7, 35, // Skip to: 13609
/* 4642 */    MCD::OPC_CheckField, 19, 1, 0, 1, 35, // Skip to: 13609
/* 4648 */    MCD::OPC_Decode, 136, 12, 127, // Opcode: SRLI_B
/* 4652 */    MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 4664
/* 4656 */    MCD::OPC_CheckPredicate, 7, 245, 34, // Skip to: 13609
/* 4660 */    MCD::OPC_Decode, 181, 1, 125, // Opcode: BCLRI_D
/* 4664 */    MCD::OPC_FilterValue, 7, 52, 0, // Skip to: 4720
/* 4668 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4671 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4683
/* 4675 */    MCD::OPC_CheckPredicate, 7, 226, 34, // Skip to: 13609
/* 4679 */    MCD::OPC_Decode, 183, 1, 119, // Opcode: BCLRI_W
/* 4683 */    MCD::OPC_FilterValue, 1, 218, 34, // Skip to: 13609
/* 4687 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4690 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4702
/* 4694 */    MCD::OPC_CheckPredicate, 7, 207, 34, // Skip to: 13609
/* 4698 */    MCD::OPC_Decode, 182, 1, 126, // Opcode: BCLRI_H
/* 4702 */    MCD::OPC_FilterValue, 1, 199, 34, // Skip to: 13609
/* 4706 */    MCD::OPC_CheckPredicate, 7, 195, 34, // Skip to: 13609
/* 4710 */    MCD::OPC_CheckField, 19, 1, 0, 189, 34, // Skip to: 13609
/* 4716 */    MCD::OPC_Decode, 180, 1, 127, // Opcode: BCLRI_B
/* 4720 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 4732
/* 4724 */    MCD::OPC_CheckPredicate, 7, 177, 34, // Skip to: 13609
/* 4728 */    MCD::OPC_Decode, 164, 2, 125, // Opcode: BSETI_D
/* 4732 */    MCD::OPC_FilterValue, 9, 52, 0, // Skip to: 4788
/* 4736 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4739 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4751
/* 4743 */    MCD::OPC_CheckPredicate, 7, 158, 34, // Skip to: 13609
/* 4747 */    MCD::OPC_Decode, 166, 2, 119, // Opcode: BSETI_W
/* 4751 */    MCD::OPC_FilterValue, 1, 150, 34, // Skip to: 13609
/* 4755 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4758 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4770
/* 4762 */    MCD::OPC_CheckPredicate, 7, 139, 34, // Skip to: 13609
/* 4766 */    MCD::OPC_Decode, 165, 2, 126, // Opcode: BSETI_H
/* 4770 */    MCD::OPC_FilterValue, 1, 131, 34, // Skip to: 13609
/* 4774 */    MCD::OPC_CheckPredicate, 7, 127, 34, // Skip to: 13609
/* 4778 */    MCD::OPC_CheckField, 19, 1, 0, 121, 34, // Skip to: 13609
/* 4784 */    MCD::OPC_Decode, 163, 2, 127, // Opcode: BSETI_B
/* 4788 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 4800
/* 4792 */    MCD::OPC_CheckPredicate, 7, 109, 34, // Skip to: 13609
/* 4796 */    MCD::OPC_Decode, 131, 2, 125, // Opcode: BNEGI_D
/* 4800 */    MCD::OPC_FilterValue, 11, 52, 0, // Skip to: 4856
/* 4804 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4807 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4819
/* 4811 */    MCD::OPC_CheckPredicate, 7, 90, 34, // Skip to: 13609
/* 4815 */    MCD::OPC_Decode, 133, 2, 119, // Opcode: BNEGI_W
/* 4819 */    MCD::OPC_FilterValue, 1, 82, 34, // Skip to: 13609
/* 4823 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4826 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 4838
/* 4830 */    MCD::OPC_CheckPredicate, 7, 71, 34, // Skip to: 13609
/* 4834 */    MCD::OPC_Decode, 132, 2, 126, // Opcode: BNEGI_H
/* 4838 */    MCD::OPC_FilterValue, 1, 63, 34, // Skip to: 13609
/* 4842 */    MCD::OPC_CheckPredicate, 7, 59, 34, // Skip to: 13609
/* 4846 */    MCD::OPC_CheckField, 19, 1, 0, 53, 34, // Skip to: 13609
/* 4852 */    MCD::OPC_Decode, 130, 2, 127, // Opcode: BNEGI_B
/* 4856 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 4869
/* 4860 */    MCD::OPC_CheckPredicate, 7, 41, 34, // Skip to: 13609
/* 4864 */    MCD::OPC_Decode, 216, 1, 128, 1, // Opcode: BINSLI_D
/* 4869 */    MCD::OPC_FilterValue, 13, 55, 0, // Skip to: 4928
/* 4873 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4876 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 4889
/* 4880 */    MCD::OPC_CheckPredicate, 7, 21, 34, // Skip to: 13609
/* 4884 */    MCD::OPC_Decode, 218, 1, 129, 1, // Opcode: BINSLI_W
/* 4889 */    MCD::OPC_FilterValue, 1, 12, 34, // Skip to: 13609
/* 4893 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4896 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 4909
/* 4900 */    MCD::OPC_CheckPredicate, 7, 1, 34, // Skip to: 13609
/* 4904 */    MCD::OPC_Decode, 217, 1, 130, 1, // Opcode: BINSLI_H
/* 4909 */    MCD::OPC_FilterValue, 1, 248, 33, // Skip to: 13609
/* 4913 */    MCD::OPC_CheckPredicate, 7, 244, 33, // Skip to: 13609
/* 4917 */    MCD::OPC_CheckField, 19, 1, 0, 238, 33, // Skip to: 13609
/* 4923 */    MCD::OPC_Decode, 215, 1, 131, 1, // Opcode: BINSLI_B
/* 4928 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 4941
/* 4932 */    MCD::OPC_CheckPredicate, 7, 225, 33, // Skip to: 13609
/* 4936 */    MCD::OPC_Decode, 224, 1, 128, 1, // Opcode: BINSRI_D
/* 4941 */    MCD::OPC_FilterValue, 15, 216, 33, // Skip to: 13609
/* 4945 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 4948 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 4961
/* 4952 */    MCD::OPC_CheckPredicate, 7, 205, 33, // Skip to: 13609
/* 4956 */    MCD::OPC_Decode, 226, 1, 129, 1, // Opcode: BINSRI_W
/* 4961 */    MCD::OPC_FilterValue, 1, 196, 33, // Skip to: 13609
/* 4965 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 4968 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 4981
/* 4972 */    MCD::OPC_CheckPredicate, 7, 185, 33, // Skip to: 13609
/* 4976 */    MCD::OPC_Decode, 225, 1, 130, 1, // Opcode: BINSRI_H
/* 4981 */    MCD::OPC_FilterValue, 1, 176, 33, // Skip to: 13609
/* 4985 */    MCD::OPC_CheckPredicate, 7, 172, 33, // Skip to: 13609
/* 4989 */    MCD::OPC_CheckField, 19, 1, 0, 166, 33, // Skip to: 13609
/* 4995 */    MCD::OPC_Decode, 223, 1, 131, 1, // Opcode: BINSRI_B
/* 5000 */    MCD::OPC_FilterValue, 10, 19, 1, // Skip to: 5279
/* 5004 */    MCD::OPC_ExtractField, 22, 4,  // Inst{25-22} ...
/* 5007 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5019
/* 5011 */    MCD::OPC_CheckPredicate, 7, 146, 33, // Skip to: 13609
/* 5015 */    MCD::OPC_Decode, 238, 10, 125, // Opcode: SAT_S_D
/* 5019 */    MCD::OPC_FilterValue, 1, 52, 0, // Skip to: 5075
/* 5023 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 5026 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5038
/* 5030 */    MCD::OPC_CheckPredicate, 7, 127, 33, // Skip to: 13609
/* 5034 */    MCD::OPC_Decode, 240, 10, 119, // Opcode: SAT_S_W
/* 5038 */    MCD::OPC_FilterValue, 1, 119, 33, // Skip to: 13609
/* 5042 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 5045 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5057
/* 5049 */    MCD::OPC_CheckPredicate, 7, 108, 33, // Skip to: 13609
/* 5053 */    MCD::OPC_Decode, 239, 10, 126, // Opcode: SAT_S_H
/* 5057 */    MCD::OPC_FilterValue, 1, 100, 33, // Skip to: 13609
/* 5061 */    MCD::OPC_CheckPredicate, 7, 96, 33, // Skip to: 13609
/* 5065 */    MCD::OPC_CheckField, 19, 1, 0, 90, 33, // Skip to: 13609
/* 5071 */    MCD::OPC_Decode, 237, 10, 127, // Opcode: SAT_S_B
/* 5075 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 5087
/* 5079 */    MCD::OPC_CheckPredicate, 7, 78, 33, // Skip to: 13609
/* 5083 */    MCD::OPC_Decode, 242, 10, 125, // Opcode: SAT_U_D
/* 5087 */    MCD::OPC_FilterValue, 3, 52, 0, // Skip to: 5143
/* 5091 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 5094 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5106
/* 5098 */    MCD::OPC_CheckPredicate, 7, 59, 33, // Skip to: 13609
/* 5102 */    MCD::OPC_Decode, 244, 10, 119, // Opcode: SAT_U_W
/* 5106 */    MCD::OPC_FilterValue, 1, 51, 33, // Skip to: 13609
/* 5110 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 5113 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5125
/* 5117 */    MCD::OPC_CheckPredicate, 7, 40, 33, // Skip to: 13609
/* 5121 */    MCD::OPC_Decode, 243, 10, 126, // Opcode: SAT_U_H
/* 5125 */    MCD::OPC_FilterValue, 1, 32, 33, // Skip to: 13609
/* 5129 */    MCD::OPC_CheckPredicate, 7, 28, 33, // Skip to: 13609
/* 5133 */    MCD::OPC_CheckField, 19, 1, 0, 22, 33, // Skip to: 13609
/* 5139 */    MCD::OPC_Decode, 241, 10, 127, // Opcode: SAT_U_B
/* 5143 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 5155
/* 5147 */    MCD::OPC_CheckPredicate, 7, 10, 33, // Skip to: 13609
/* 5151 */    MCD::OPC_Decode, 248, 11, 125, // Opcode: SRARI_D
/* 5155 */    MCD::OPC_FilterValue, 5, 52, 0, // Skip to: 5211
/* 5159 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 5162 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5174
/* 5166 */    MCD::OPC_CheckPredicate, 7, 247, 32, // Skip to: 13609
/* 5170 */    MCD::OPC_Decode, 250, 11, 119, // Opcode: SRARI_W
/* 5174 */    MCD::OPC_FilterValue, 1, 239, 32, // Skip to: 13609
/* 5178 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 5181 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5193
/* 5185 */    MCD::OPC_CheckPredicate, 7, 228, 32, // Skip to: 13609
/* 5189 */    MCD::OPC_Decode, 249, 11, 126, // Opcode: SRARI_H
/* 5193 */    MCD::OPC_FilterValue, 1, 220, 32, // Skip to: 13609
/* 5197 */    MCD::OPC_CheckPredicate, 7, 216, 32, // Skip to: 13609
/* 5201 */    MCD::OPC_CheckField, 19, 1, 0, 210, 32, // Skip to: 13609
/* 5207 */    MCD::OPC_Decode, 247, 11, 127, // Opcode: SRARI_B
/* 5211 */    MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 5223
/* 5215 */    MCD::OPC_CheckPredicate, 7, 198, 32, // Skip to: 13609
/* 5219 */    MCD::OPC_Decode, 141, 12, 125, // Opcode: SRLRI_D
/* 5223 */    MCD::OPC_FilterValue, 7, 190, 32, // Skip to: 13609
/* 5227 */    MCD::OPC_ExtractField, 21, 1,  // Inst{21} ...
/* 5230 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5242
/* 5234 */    MCD::OPC_CheckPredicate, 7, 179, 32, // Skip to: 13609
/* 5238 */    MCD::OPC_Decode, 143, 12, 119, // Opcode: SRLRI_W
/* 5242 */    MCD::OPC_FilterValue, 1, 171, 32, // Skip to: 13609
/* 5246 */    MCD::OPC_ExtractField, 20, 1,  // Inst{20} ...
/* 5249 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5261
/* 5253 */    MCD::OPC_CheckPredicate, 7, 160, 32, // Skip to: 13609
/* 5257 */    MCD::OPC_Decode, 142, 12, 126, // Opcode: SRLRI_H
/* 5261 */    MCD::OPC_FilterValue, 1, 152, 32, // Skip to: 13609
/* 5265 */    MCD::OPC_CheckPredicate, 7, 148, 32, // Skip to: 13609
/* 5269 */    MCD::OPC_CheckField, 19, 1, 0, 142, 32, // Skip to: 13609
/* 5275 */    MCD::OPC_Decode, 140, 12, 127, // Opcode: SRLRI_B
/* 5279 */    MCD::OPC_FilterValue, 13, 163, 1, // Skip to: 5702
/* 5283 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 5286 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 5299
/* 5290 */    MCD::OPC_CheckPredicate, 7, 123, 32, // Skip to: 13609
/* 5294 */    MCD::OPC_Decode, 210, 11, 132, 1, // Opcode: SLL_B
/* 5299 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 5312
/* 5303 */    MCD::OPC_CheckPredicate, 7, 110, 32, // Skip to: 13609
/* 5307 */    MCD::OPC_Decode, 212, 11, 133, 1, // Opcode: SLL_H
/* 5312 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 5325
/* 5316 */    MCD::OPC_CheckPredicate, 7, 97, 32, // Skip to: 13609
/* 5320 */    MCD::OPC_Decode, 214, 11, 134, 1, // Opcode: SLL_W
/* 5325 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 5338
/* 5329 */    MCD::OPC_CheckPredicate, 7, 84, 32, // Skip to: 13609
/* 5333 */    MCD::OPC_Decode, 211, 11, 135, 1, // Opcode: SLL_D
/* 5338 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 5351
/* 5342 */    MCD::OPC_CheckPredicate, 7, 71, 32, // Skip to: 13609
/* 5346 */    MCD::OPC_Decode, 129, 12, 132, 1, // Opcode: SRA_B
/* 5351 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 5364
/* 5355 */    MCD::OPC_CheckPredicate, 7, 58, 32, // Skip to: 13609
/* 5359 */    MCD::OPC_Decode, 131, 12, 133, 1, // Opcode: SRA_H
/* 5364 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 5377
/* 5368 */    MCD::OPC_CheckPredicate, 7, 45, 32, // Skip to: 13609
/* 5372 */    MCD::OPC_Decode, 133, 12, 134, 1, // Opcode: SRA_W
/* 5377 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 5390
/* 5381 */    MCD::OPC_CheckPredicate, 7, 32, 32, // Skip to: 13609
/* 5385 */    MCD::OPC_Decode, 130, 12, 135, 1, // Opcode: SRA_D
/* 5390 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 5403
/* 5394 */    MCD::OPC_CheckPredicate, 7, 19, 32, // Skip to: 13609
/* 5398 */    MCD::OPC_Decode, 150, 12, 132, 1, // Opcode: SRL_B
/* 5403 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 5416
/* 5407 */    MCD::OPC_CheckPredicate, 7, 6, 32, // Skip to: 13609
/* 5411 */    MCD::OPC_Decode, 152, 12, 133, 1, // Opcode: SRL_H
/* 5416 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 5429
/* 5420 */    MCD::OPC_CheckPredicate, 7, 249, 31, // Skip to: 13609
/* 5424 */    MCD::OPC_Decode, 154, 12, 134, 1, // Opcode: SRL_W
/* 5429 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 5442
/* 5433 */    MCD::OPC_CheckPredicate, 7, 236, 31, // Skip to: 13609
/* 5437 */    MCD::OPC_Decode, 151, 12, 135, 1, // Opcode: SRL_D
/* 5442 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 5455
/* 5446 */    MCD::OPC_CheckPredicate, 7, 223, 31, // Skip to: 13609
/* 5450 */    MCD::OPC_Decode, 184, 1, 132, 1, // Opcode: BCLR_B
/* 5455 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 5468
/* 5459 */    MCD::OPC_CheckPredicate, 7, 210, 31, // Skip to: 13609
/* 5463 */    MCD::OPC_Decode, 186, 1, 133, 1, // Opcode: BCLR_H
/* 5468 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 5481
/* 5472 */    MCD::OPC_CheckPredicate, 7, 197, 31, // Skip to: 13609
/* 5476 */    MCD::OPC_Decode, 187, 1, 134, 1, // Opcode: BCLR_W
/* 5481 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 5494
/* 5485 */    MCD::OPC_CheckPredicate, 7, 184, 31, // Skip to: 13609
/* 5489 */    MCD::OPC_Decode, 185, 1, 135, 1, // Opcode: BCLR_D
/* 5494 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 5507
/* 5498 */    MCD::OPC_CheckPredicate, 7, 171, 31, // Skip to: 13609
/* 5502 */    MCD::OPC_Decode, 167, 2, 132, 1, // Opcode: BSET_B
/* 5507 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 5520
/* 5511 */    MCD::OPC_CheckPredicate, 7, 158, 31, // Skip to: 13609
/* 5515 */    MCD::OPC_Decode, 169, 2, 133, 1, // Opcode: BSET_H
/* 5520 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 5533
/* 5524 */    MCD::OPC_CheckPredicate, 7, 145, 31, // Skip to: 13609
/* 5528 */    MCD::OPC_Decode, 170, 2, 134, 1, // Opcode: BSET_W
/* 5533 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 5546
/* 5537 */    MCD::OPC_CheckPredicate, 7, 132, 31, // Skip to: 13609
/* 5541 */    MCD::OPC_Decode, 168, 2, 135, 1, // Opcode: BSET_D
/* 5546 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 5559
/* 5550 */    MCD::OPC_CheckPredicate, 7, 119, 31, // Skip to: 13609
/* 5554 */    MCD::OPC_Decode, 134, 2, 132, 1, // Opcode: BNEG_B
/* 5559 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 5572
/* 5563 */    MCD::OPC_CheckPredicate, 7, 106, 31, // Skip to: 13609
/* 5567 */    MCD::OPC_Decode, 136, 2, 133, 1, // Opcode: BNEG_H
/* 5572 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 5585
/* 5576 */    MCD::OPC_CheckPredicate, 7, 93, 31, // Skip to: 13609
/* 5580 */    MCD::OPC_Decode, 137, 2, 134, 1, // Opcode: BNEG_W
/* 5585 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 5598
/* 5589 */    MCD::OPC_CheckPredicate, 7, 80, 31, // Skip to: 13609
/* 5593 */    MCD::OPC_Decode, 135, 2, 135, 1, // Opcode: BNEG_D
/* 5598 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 5611
/* 5602 */    MCD::OPC_CheckPredicate, 7, 67, 31, // Skip to: 13609
/* 5606 */    MCD::OPC_Decode, 219, 1, 136, 1, // Opcode: BINSL_B
/* 5611 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 5624
/* 5615 */    MCD::OPC_CheckPredicate, 7, 54, 31, // Skip to: 13609
/* 5619 */    MCD::OPC_Decode, 221, 1, 137, 1, // Opcode: BINSL_H
/* 5624 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 5637
/* 5628 */    MCD::OPC_CheckPredicate, 7, 41, 31, // Skip to: 13609
/* 5632 */    MCD::OPC_Decode, 222, 1, 138, 1, // Opcode: BINSL_W
/* 5637 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 5650
/* 5641 */    MCD::OPC_CheckPredicate, 7, 28, 31, // Skip to: 13609
/* 5645 */    MCD::OPC_Decode, 220, 1, 139, 1, // Opcode: BINSL_D
/* 5650 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 5663
/* 5654 */    MCD::OPC_CheckPredicate, 7, 15, 31, // Skip to: 13609
/* 5658 */    MCD::OPC_Decode, 227, 1, 136, 1, // Opcode: BINSR_B
/* 5663 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 5676
/* 5667 */    MCD::OPC_CheckPredicate, 7, 2, 31, // Skip to: 13609
/* 5671 */    MCD::OPC_Decode, 229, 1, 137, 1, // Opcode: BINSR_H
/* 5676 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 5689
/* 5680 */    MCD::OPC_CheckPredicate, 7, 245, 30, // Skip to: 13609
/* 5684 */    MCD::OPC_Decode, 230, 1, 138, 1, // Opcode: BINSR_W
/* 5689 */    MCD::OPC_FilterValue, 31, 236, 30, // Skip to: 13609
/* 5693 */    MCD::OPC_CheckPredicate, 7, 232, 30, // Skip to: 13609
/* 5697 */    MCD::OPC_Decode, 228, 1, 139, 1, // Opcode: BINSR_D
/* 5702 */    MCD::OPC_FilterValue, 14, 159, 1, // Skip to: 6121
/* 5706 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 5709 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 5721
/* 5713 */    MCD::OPC_CheckPredicate, 7, 212, 30, // Skip to: 13609
/* 5717 */    MCD::OPC_Decode, 62, 132, 1, // Opcode: ADDV_B
/* 5721 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 5733
/* 5725 */    MCD::OPC_CheckPredicate, 7, 200, 30, // Skip to: 13609
/* 5729 */    MCD::OPC_Decode, 64, 133, 1, // Opcode: ADDV_H
/* 5733 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 5745
/* 5737 */    MCD::OPC_CheckPredicate, 7, 188, 30, // Skip to: 13609
/* 5741 */    MCD::OPC_Decode, 65, 134, 1, // Opcode: ADDV_W
/* 5745 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 5757
/* 5749 */    MCD::OPC_CheckPredicate, 7, 176, 30, // Skip to: 13609
/* 5753 */    MCD::OPC_Decode, 63, 135, 1, // Opcode: ADDV_D
/* 5757 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 5770
/* 5761 */    MCD::OPC_CheckPredicate, 7, 164, 30, // Skip to: 13609
/* 5765 */    MCD::OPC_Decode, 200, 12, 132, 1, // Opcode: SUBV_B
/* 5770 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 5783
/* 5774 */    MCD::OPC_CheckPredicate, 7, 151, 30, // Skip to: 13609
/* 5778 */    MCD::OPC_Decode, 202, 12, 133, 1, // Opcode: SUBV_H
/* 5783 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 5796
/* 5787 */    MCD::OPC_CheckPredicate, 7, 138, 30, // Skip to: 13609
/* 5791 */    MCD::OPC_Decode, 203, 12, 134, 1, // Opcode: SUBV_W
/* 5796 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 5809
/* 5800 */    MCD::OPC_CheckPredicate, 7, 125, 30, // Skip to: 13609
/* 5804 */    MCD::OPC_Decode, 201, 12, 135, 1, // Opcode: SUBV_D
/* 5809 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 5822
/* 5813 */    MCD::OPC_CheckPredicate, 7, 112, 30, // Skip to: 13609
/* 5817 */    MCD::OPC_Decode, 147, 8, 132, 1, // Opcode: MAX_S_B
/* 5822 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 5835
/* 5826 */    MCD::OPC_CheckPredicate, 7, 99, 30, // Skip to: 13609
/* 5830 */    MCD::OPC_Decode, 149, 8, 133, 1, // Opcode: MAX_S_H
/* 5835 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 5848
/* 5839 */    MCD::OPC_CheckPredicate, 7, 86, 30, // Skip to: 13609
/* 5843 */    MCD::OPC_Decode, 150, 8, 134, 1, // Opcode: MAX_S_W
/* 5848 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 5861
/* 5852 */    MCD::OPC_CheckPredicate, 7, 73, 30, // Skip to: 13609
/* 5856 */    MCD::OPC_Decode, 148, 8, 135, 1, // Opcode: MAX_S_D
/* 5861 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 5874
/* 5865 */    MCD::OPC_CheckPredicate, 7, 60, 30, // Skip to: 13609
/* 5869 */    MCD::OPC_Decode, 151, 8, 132, 1, // Opcode: MAX_U_B
/* 5874 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 5887
/* 5878 */    MCD::OPC_CheckPredicate, 7, 47, 30, // Skip to: 13609
/* 5882 */    MCD::OPC_Decode, 153, 8, 133, 1, // Opcode: MAX_U_H
/* 5887 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 5900
/* 5891 */    MCD::OPC_CheckPredicate, 7, 34, 30, // Skip to: 13609
/* 5895 */    MCD::OPC_Decode, 154, 8, 134, 1, // Opcode: MAX_U_W
/* 5900 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 5913
/* 5904 */    MCD::OPC_CheckPredicate, 7, 21, 30, // Skip to: 13609
/* 5908 */    MCD::OPC_Decode, 152, 8, 135, 1, // Opcode: MAX_U_D
/* 5913 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 5926
/* 5917 */    MCD::OPC_CheckPredicate, 7, 8, 30, // Skip to: 13609
/* 5921 */    MCD::OPC_Decode, 188, 8, 132, 1, // Opcode: MIN_S_B
/* 5926 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 5939
/* 5930 */    MCD::OPC_CheckPredicate, 7, 251, 29, // Skip to: 13609
/* 5934 */    MCD::OPC_Decode, 190, 8, 133, 1, // Opcode: MIN_S_H
/* 5939 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 5952
/* 5943 */    MCD::OPC_CheckPredicate, 7, 238, 29, // Skip to: 13609
/* 5947 */    MCD::OPC_Decode, 191, 8, 134, 1, // Opcode: MIN_S_W
/* 5952 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 5965
/* 5956 */    MCD::OPC_CheckPredicate, 7, 225, 29, // Skip to: 13609
/* 5960 */    MCD::OPC_Decode, 189, 8, 135, 1, // Opcode: MIN_S_D
/* 5965 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 5978
/* 5969 */    MCD::OPC_CheckPredicate, 7, 212, 29, // Skip to: 13609
/* 5973 */    MCD::OPC_Decode, 192, 8, 132, 1, // Opcode: MIN_U_B
/* 5978 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 5991
/* 5982 */    MCD::OPC_CheckPredicate, 7, 199, 29, // Skip to: 13609
/* 5986 */    MCD::OPC_Decode, 194, 8, 133, 1, // Opcode: MIN_U_H
/* 5991 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 6004
/* 5995 */    MCD::OPC_CheckPredicate, 7, 186, 29, // Skip to: 13609
/* 5999 */    MCD::OPC_Decode, 195, 8, 134, 1, // Opcode: MIN_U_W
/* 6004 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 6017
/* 6008 */    MCD::OPC_CheckPredicate, 7, 173, 29, // Skip to: 13609
/* 6012 */    MCD::OPC_Decode, 193, 8, 135, 1, // Opcode: MIN_U_D
/* 6017 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 6030
/* 6021 */    MCD::OPC_CheckPredicate, 7, 160, 29, // Skip to: 13609
/* 6025 */    MCD::OPC_Decode, 141, 8, 132, 1, // Opcode: MAX_A_B
/* 6030 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 6043
/* 6034 */    MCD::OPC_CheckPredicate, 7, 147, 29, // Skip to: 13609
/* 6038 */    MCD::OPC_Decode, 143, 8, 133, 1, // Opcode: MAX_A_H
/* 6043 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 6056
/* 6047 */    MCD::OPC_CheckPredicate, 7, 134, 29, // Skip to: 13609
/* 6051 */    MCD::OPC_Decode, 144, 8, 134, 1, // Opcode: MAX_A_W
/* 6056 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 6069
/* 6060 */    MCD::OPC_CheckPredicate, 7, 121, 29, // Skip to: 13609
/* 6064 */    MCD::OPC_Decode, 142, 8, 135, 1, // Opcode: MAX_A_D
/* 6069 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 6082
/* 6073 */    MCD::OPC_CheckPredicate, 7, 108, 29, // Skip to: 13609
/* 6077 */    MCD::OPC_Decode, 182, 8, 132, 1, // Opcode: MIN_A_B
/* 6082 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 6095
/* 6086 */    MCD::OPC_CheckPredicate, 7, 95, 29, // Skip to: 13609
/* 6090 */    MCD::OPC_Decode, 184, 8, 133, 1, // Opcode: MIN_A_H
/* 6095 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 6108
/* 6099 */    MCD::OPC_CheckPredicate, 7, 82, 29, // Skip to: 13609
/* 6103 */    MCD::OPC_Decode, 185, 8, 134, 1, // Opcode: MIN_A_W
/* 6108 */    MCD::OPC_FilterValue, 31, 73, 29, // Skip to: 13609
/* 6112 */    MCD::OPC_CheckPredicate, 7, 69, 29, // Skip to: 13609
/* 6116 */    MCD::OPC_Decode, 183, 8, 135, 1, // Opcode: MIN_A_D
/* 6121 */    MCD::OPC_FilterValue, 15, 7, 1, // Skip to: 6388
/* 6125 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 6128 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 6141
/* 6132 */    MCD::OPC_CheckPredicate, 7, 49, 29, // Skip to: 13609
/* 6136 */    MCD::OPC_Decode, 215, 2, 132, 1, // Opcode: CEQ_B
/* 6141 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 6154
/* 6145 */    MCD::OPC_CheckPredicate, 7, 36, 29, // Skip to: 13609
/* 6149 */    MCD::OPC_Decode, 217, 2, 133, 1, // Opcode: CEQ_H
/* 6154 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 6167
/* 6158 */    MCD::OPC_CheckPredicate, 7, 23, 29, // Skip to: 13609
/* 6162 */    MCD::OPC_Decode, 218, 2, 134, 1, // Opcode: CEQ_W
/* 6167 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 6180
/* 6171 */    MCD::OPC_CheckPredicate, 7, 10, 29, // Skip to: 13609
/* 6175 */    MCD::OPC_Decode, 216, 2, 135, 1, // Opcode: CEQ_D
/* 6180 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 6193
/* 6184 */    MCD::OPC_CheckPredicate, 7, 253, 28, // Skip to: 13609
/* 6188 */    MCD::OPC_Decode, 253, 2, 132, 1, // Opcode: CLT_S_B
/* 6193 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 6206
/* 6197 */    MCD::OPC_CheckPredicate, 7, 240, 28, // Skip to: 13609
/* 6201 */    MCD::OPC_Decode, 255, 2, 133, 1, // Opcode: CLT_S_H
/* 6206 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 6219
/* 6210 */    MCD::OPC_CheckPredicate, 7, 227, 28, // Skip to: 13609
/* 6214 */    MCD::OPC_Decode, 128, 3, 134, 1, // Opcode: CLT_S_W
/* 6219 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 6232
/* 6223 */    MCD::OPC_CheckPredicate, 7, 214, 28, // Skip to: 13609
/* 6227 */    MCD::OPC_Decode, 254, 2, 135, 1, // Opcode: CLT_S_D
/* 6232 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 6245
/* 6236 */    MCD::OPC_CheckPredicate, 7, 201, 28, // Skip to: 13609
/* 6240 */    MCD::OPC_Decode, 129, 3, 132, 1, // Opcode: CLT_U_B
/* 6245 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 6258
/* 6249 */    MCD::OPC_CheckPredicate, 7, 188, 28, // Skip to: 13609
/* 6253 */    MCD::OPC_Decode, 131, 3, 133, 1, // Opcode: CLT_U_H
/* 6258 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 6271
/* 6262 */    MCD::OPC_CheckPredicate, 7, 175, 28, // Skip to: 13609
/* 6266 */    MCD::OPC_Decode, 132, 3, 134, 1, // Opcode: CLT_U_W
/* 6271 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 6284
/* 6275 */    MCD::OPC_CheckPredicate, 7, 162, 28, // Skip to: 13609
/* 6279 */    MCD::OPC_Decode, 130, 3, 135, 1, // Opcode: CLT_U_D
/* 6284 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 6297
/* 6288 */    MCD::OPC_CheckPredicate, 7, 149, 28, // Skip to: 13609
/* 6292 */    MCD::OPC_Decode, 234, 2, 132, 1, // Opcode: CLE_S_B
/* 6297 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 6310
/* 6301 */    MCD::OPC_CheckPredicate, 7, 136, 28, // Skip to: 13609
/* 6305 */    MCD::OPC_Decode, 236, 2, 133, 1, // Opcode: CLE_S_H
/* 6310 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 6323
/* 6314 */    MCD::OPC_CheckPredicate, 7, 123, 28, // Skip to: 13609
/* 6318 */    MCD::OPC_Decode, 237, 2, 134, 1, // Opcode: CLE_S_W
/* 6323 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 6336
/* 6327 */    MCD::OPC_CheckPredicate, 7, 110, 28, // Skip to: 13609
/* 6331 */    MCD::OPC_Decode, 235, 2, 135, 1, // Opcode: CLE_S_D
/* 6336 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 6349
/* 6340 */    MCD::OPC_CheckPredicate, 7, 97, 28, // Skip to: 13609
/* 6344 */    MCD::OPC_Decode, 238, 2, 132, 1, // Opcode: CLE_U_B
/* 6349 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 6362
/* 6353 */    MCD::OPC_CheckPredicate, 7, 84, 28, // Skip to: 13609
/* 6357 */    MCD::OPC_Decode, 240, 2, 133, 1, // Opcode: CLE_U_H
/* 6362 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 6375
/* 6366 */    MCD::OPC_CheckPredicate, 7, 71, 28, // Skip to: 13609
/* 6370 */    MCD::OPC_Decode, 241, 2, 134, 1, // Opcode: CLE_U_W
/* 6375 */    MCD::OPC_FilterValue, 23, 62, 28, // Skip to: 13609
/* 6379 */    MCD::OPC_CheckPredicate, 7, 58, 28, // Skip to: 13609
/* 6383 */    MCD::OPC_Decode, 239, 2, 135, 1, // Opcode: CLE_U_D
/* 6388 */    MCD::OPC_FilterValue, 16, 147, 1, // Skip to: 6795
/* 6392 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 6395 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 6407
/* 6399 */    MCD::OPC_CheckPredicate, 7, 38, 28, // Skip to: 13609
/* 6403 */    MCD::OPC_Decode, 67, 132, 1, // Opcode: ADD_A_B
/* 6407 */    MCD::OPC_FilterValue, 1, 8, 0, // Skip to: 6419
/* 6411 */    MCD::OPC_CheckPredicate, 7, 26, 28, // Skip to: 13609
/* 6415 */    MCD::OPC_Decode, 69, 133, 1, // Opcode: ADD_A_H
/* 6419 */    MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 6431
/* 6423 */    MCD::OPC_CheckPredicate, 7, 14, 28, // Skip to: 13609
/* 6427 */    MCD::OPC_Decode, 70, 134, 1, // Opcode: ADD_A_W
/* 6431 */    MCD::OPC_FilterValue, 3, 8, 0, // Skip to: 6443
/* 6435 */    MCD::OPC_CheckPredicate, 7, 2, 28, // Skip to: 13609
/* 6439 */    MCD::OPC_Decode, 68, 135, 1, // Opcode: ADD_A_D
/* 6443 */    MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 6455
/* 6447 */    MCD::OPC_CheckPredicate, 7, 246, 27, // Skip to: 13609
/* 6451 */    MCD::OPC_Decode, 39, 132, 1, // Opcode: ADDS_A_B
/* 6455 */    MCD::OPC_FilterValue, 5, 8, 0, // Skip to: 6467
/* 6459 */    MCD::OPC_CheckPredicate, 7, 234, 27, // Skip to: 13609
/* 6463 */    MCD::OPC_Decode, 41, 133, 1, // Opcode: ADDS_A_H
/* 6467 */    MCD::OPC_FilterValue, 6, 8, 0, // Skip to: 6479
/* 6471 */    MCD::OPC_CheckPredicate, 7, 222, 27, // Skip to: 13609
/* 6475 */    MCD::OPC_Decode, 42, 134, 1, // Opcode: ADDS_A_W
/* 6479 */    MCD::OPC_FilterValue, 7, 8, 0, // Skip to: 6491
/* 6483 */    MCD::OPC_CheckPredicate, 7, 210, 27, // Skip to: 13609
/* 6487 */    MCD::OPC_Decode, 40, 135, 1, // Opcode: ADDS_A_D
/* 6491 */    MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 6503
/* 6495 */    MCD::OPC_CheckPredicate, 7, 198, 27, // Skip to: 13609
/* 6499 */    MCD::OPC_Decode, 43, 132, 1, // Opcode: ADDS_S_B
/* 6503 */    MCD::OPC_FilterValue, 9, 8, 0, // Skip to: 6515
/* 6507 */    MCD::OPC_CheckPredicate, 7, 186, 27, // Skip to: 13609
/* 6511 */    MCD::OPC_Decode, 45, 133, 1, // Opcode: ADDS_S_H
/* 6515 */    MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 6527
/* 6519 */    MCD::OPC_CheckPredicate, 7, 174, 27, // Skip to: 13609
/* 6523 */    MCD::OPC_Decode, 46, 134, 1, // Opcode: ADDS_S_W
/* 6527 */    MCD::OPC_FilterValue, 11, 8, 0, // Skip to: 6539
/* 6531 */    MCD::OPC_CheckPredicate, 7, 162, 27, // Skip to: 13609
/* 6535 */    MCD::OPC_Decode, 44, 135, 1, // Opcode: ADDS_S_D
/* 6539 */    MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 6551
/* 6543 */    MCD::OPC_CheckPredicate, 7, 150, 27, // Skip to: 13609
/* 6547 */    MCD::OPC_Decode, 47, 132, 1, // Opcode: ADDS_U_B
/* 6551 */    MCD::OPC_FilterValue, 13, 8, 0, // Skip to: 6563
/* 6555 */    MCD::OPC_CheckPredicate, 7, 138, 27, // Skip to: 13609
/* 6559 */    MCD::OPC_Decode, 49, 133, 1, // Opcode: ADDS_U_H
/* 6563 */    MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 6575
/* 6567 */    MCD::OPC_CheckPredicate, 7, 126, 27, // Skip to: 13609
/* 6571 */    MCD::OPC_Decode, 50, 134, 1, // Opcode: ADDS_U_W
/* 6575 */    MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 6587
/* 6579 */    MCD::OPC_CheckPredicate, 7, 114, 27, // Skip to: 13609
/* 6583 */    MCD::OPC_Decode, 48, 135, 1, // Opcode: ADDS_U_D
/* 6587 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 6600
/* 6591 */    MCD::OPC_CheckPredicate, 7, 102, 27, // Skip to: 13609
/* 6595 */    MCD::OPC_Decode, 146, 1, 132, 1, // Opcode: AVE_S_B
/* 6600 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 6613
/* 6604 */    MCD::OPC_CheckPredicate, 7, 89, 27, // Skip to: 13609
/* 6608 */    MCD::OPC_Decode, 148, 1, 133, 1, // Opcode: AVE_S_H
/* 6613 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 6626
/* 6617 */    MCD::OPC_CheckPredicate, 7, 76, 27, // Skip to: 13609
/* 6621 */    MCD::OPC_Decode, 149, 1, 134, 1, // Opcode: AVE_S_W
/* 6626 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 6639
/* 6630 */    MCD::OPC_CheckPredicate, 7, 63, 27, // Skip to: 13609
/* 6634 */    MCD::OPC_Decode, 147, 1, 135, 1, // Opcode: AVE_S_D
/* 6639 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 6652
/* 6643 */    MCD::OPC_CheckPredicate, 7, 50, 27, // Skip to: 13609
/* 6647 */    MCD::OPC_Decode, 150, 1, 132, 1, // Opcode: AVE_U_B
/* 6652 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 6665
/* 6656 */    MCD::OPC_CheckPredicate, 7, 37, 27, // Skip to: 13609
/* 6660 */    MCD::OPC_Decode, 152, 1, 133, 1, // Opcode: AVE_U_H
/* 6665 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 6678
/* 6669 */    MCD::OPC_CheckPredicate, 7, 24, 27, // Skip to: 13609
/* 6673 */    MCD::OPC_Decode, 153, 1, 134, 1, // Opcode: AVE_U_W
/* 6678 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 6691
/* 6682 */    MCD::OPC_CheckPredicate, 7, 11, 27, // Skip to: 13609
/* 6686 */    MCD::OPC_Decode, 151, 1, 135, 1, // Opcode: AVE_U_D
/* 6691 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 6704
/* 6695 */    MCD::OPC_CheckPredicate, 7, 254, 26, // Skip to: 13609
/* 6699 */    MCD::OPC_Decode, 138, 1, 132, 1, // Opcode: AVER_S_B
/* 6704 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 6717
/* 6708 */    MCD::OPC_CheckPredicate, 7, 241, 26, // Skip to: 13609
/* 6712 */    MCD::OPC_Decode, 140, 1, 133, 1, // Opcode: AVER_S_H
/* 6717 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 6730
/* 6721 */    MCD::OPC_CheckPredicate, 7, 228, 26, // Skip to: 13609
/* 6725 */    MCD::OPC_Decode, 141, 1, 134, 1, // Opcode: AVER_S_W
/* 6730 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 6743
/* 6734 */    MCD::OPC_CheckPredicate, 7, 215, 26, // Skip to: 13609
/* 6738 */    MCD::OPC_Decode, 139, 1, 135, 1, // Opcode: AVER_S_D
/* 6743 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 6756
/* 6747 */    MCD::OPC_CheckPredicate, 7, 202, 26, // Skip to: 13609
/* 6751 */    MCD::OPC_Decode, 142, 1, 132, 1, // Opcode: AVER_U_B
/* 6756 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 6769
/* 6760 */    MCD::OPC_CheckPredicate, 7, 189, 26, // Skip to: 13609
/* 6764 */    MCD::OPC_Decode, 144, 1, 133, 1, // Opcode: AVER_U_H
/* 6769 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 6782
/* 6773 */    MCD::OPC_CheckPredicate, 7, 176, 26, // Skip to: 13609
/* 6777 */    MCD::OPC_Decode, 145, 1, 134, 1, // Opcode: AVER_U_W
/* 6782 */    MCD::OPC_FilterValue, 31, 167, 26, // Skip to: 13609
/* 6786 */    MCD::OPC_CheckPredicate, 7, 163, 26, // Skip to: 13609
/* 6790 */    MCD::OPC_Decode, 143, 1, 135, 1, // Opcode: AVER_U_D
/* 6795 */    MCD::OPC_FilterValue, 17, 51, 1, // Skip to: 7106
/* 6799 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 6802 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 6815
/* 6806 */    MCD::OPC_CheckPredicate, 7, 143, 26, // Skip to: 13609
/* 6810 */    MCD::OPC_Decode, 181, 12, 132, 1, // Opcode: SUBS_S_B
/* 6815 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 6828
/* 6819 */    MCD::OPC_CheckPredicate, 7, 130, 26, // Skip to: 13609
/* 6823 */    MCD::OPC_Decode, 183, 12, 133, 1, // Opcode: SUBS_S_H
/* 6828 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 6841
/* 6832 */    MCD::OPC_CheckPredicate, 7, 117, 26, // Skip to: 13609
/* 6836 */    MCD::OPC_Decode, 184, 12, 134, 1, // Opcode: SUBS_S_W
/* 6841 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 6854
/* 6845 */    MCD::OPC_CheckPredicate, 7, 104, 26, // Skip to: 13609
/* 6849 */    MCD::OPC_Decode, 182, 12, 135, 1, // Opcode: SUBS_S_D
/* 6854 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 6867
/* 6858 */    MCD::OPC_CheckPredicate, 7, 91, 26, // Skip to: 13609
/* 6862 */    MCD::OPC_Decode, 185, 12, 132, 1, // Opcode: SUBS_U_B
/* 6867 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 6880
/* 6871 */    MCD::OPC_CheckPredicate, 7, 78, 26, // Skip to: 13609
/* 6875 */    MCD::OPC_Decode, 187, 12, 133, 1, // Opcode: SUBS_U_H
/* 6880 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 6893
/* 6884 */    MCD::OPC_CheckPredicate, 7, 65, 26, // Skip to: 13609
/* 6888 */    MCD::OPC_Decode, 188, 12, 134, 1, // Opcode: SUBS_U_W
/* 6893 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 6906
/* 6897 */    MCD::OPC_CheckPredicate, 7, 52, 26, // Skip to: 13609
/* 6901 */    MCD::OPC_Decode, 186, 12, 135, 1, // Opcode: SUBS_U_D
/* 6906 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 6919
/* 6910 */    MCD::OPC_CheckPredicate, 7, 39, 26, // Skip to: 13609
/* 6914 */    MCD::OPC_Decode, 173, 12, 132, 1, // Opcode: SUBSUS_U_B
/* 6919 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 6932
/* 6923 */    MCD::OPC_CheckPredicate, 7, 26, 26, // Skip to: 13609
/* 6927 */    MCD::OPC_Decode, 175, 12, 133, 1, // Opcode: SUBSUS_U_H
/* 6932 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 6945
/* 6936 */    MCD::OPC_CheckPredicate, 7, 13, 26, // Skip to: 13609
/* 6940 */    MCD::OPC_Decode, 176, 12, 134, 1, // Opcode: SUBSUS_U_W
/* 6945 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 6958
/* 6949 */    MCD::OPC_CheckPredicate, 7, 0, 26, // Skip to: 13609
/* 6953 */    MCD::OPC_Decode, 174, 12, 135, 1, // Opcode: SUBSUS_U_D
/* 6958 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 6971
/* 6962 */    MCD::OPC_CheckPredicate, 7, 243, 25, // Skip to: 13609
/* 6966 */    MCD::OPC_Decode, 177, 12, 132, 1, // Opcode: SUBSUU_S_B
/* 6971 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 6984
/* 6975 */    MCD::OPC_CheckPredicate, 7, 230, 25, // Skip to: 13609
/* 6979 */    MCD::OPC_Decode, 179, 12, 133, 1, // Opcode: SUBSUU_S_H
/* 6984 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 6997
/* 6988 */    MCD::OPC_CheckPredicate, 7, 217, 25, // Skip to: 13609
/* 6992 */    MCD::OPC_Decode, 180, 12, 134, 1, // Opcode: SUBSUU_S_W
/* 6997 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 7010
/* 7001 */    MCD::OPC_CheckPredicate, 7, 204, 25, // Skip to: 13609
/* 7005 */    MCD::OPC_Decode, 178, 12, 135, 1, // Opcode: SUBSUU_S_D
/* 7010 */    MCD::OPC_FilterValue, 16, 8, 0, // Skip to: 7022
/* 7014 */    MCD::OPC_CheckPredicate, 7, 191, 25, // Skip to: 13609
/* 7018 */    MCD::OPC_Decode, 96, 132, 1, // Opcode: ASUB_S_B
/* 7022 */    MCD::OPC_FilterValue, 17, 8, 0, // Skip to: 7034
/* 7026 */    MCD::OPC_CheckPredicate, 7, 179, 25, // Skip to: 13609
/* 7030 */    MCD::OPC_Decode, 98, 133, 1, // Opcode: ASUB_S_H
/* 7034 */    MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 7046
/* 7038 */    MCD::OPC_CheckPredicate, 7, 167, 25, // Skip to: 13609
/* 7042 */    MCD::OPC_Decode, 99, 134, 1, // Opcode: ASUB_S_W
/* 7046 */    MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 7058
/* 7050 */    MCD::OPC_CheckPredicate, 7, 155, 25, // Skip to: 13609
/* 7054 */    MCD::OPC_Decode, 97, 135, 1, // Opcode: ASUB_S_D
/* 7058 */    MCD::OPC_FilterValue, 20, 8, 0, // Skip to: 7070
/* 7062 */    MCD::OPC_CheckPredicate, 7, 143, 25, // Skip to: 13609
/* 7066 */    MCD::OPC_Decode, 100, 132, 1, // Opcode: ASUB_U_B
/* 7070 */    MCD::OPC_FilterValue, 21, 8, 0, // Skip to: 7082
/* 7074 */    MCD::OPC_CheckPredicate, 7, 131, 25, // Skip to: 13609
/* 7078 */    MCD::OPC_Decode, 102, 133, 1, // Opcode: ASUB_U_H
/* 7082 */    MCD::OPC_FilterValue, 22, 8, 0, // Skip to: 7094
/* 7086 */    MCD::OPC_CheckPredicate, 7, 119, 25, // Skip to: 13609
/* 7090 */    MCD::OPC_Decode, 103, 134, 1, // Opcode: ASUB_U_W
/* 7094 */    MCD::OPC_FilterValue, 23, 111, 25, // Skip to: 13609
/* 7098 */    MCD::OPC_CheckPredicate, 7, 107, 25, // Skip to: 13609
/* 7102 */    MCD::OPC_Decode, 101, 135, 1, // Opcode: ASUB_U_D
/* 7106 */    MCD::OPC_FilterValue, 18, 111, 1, // Skip to: 7477
/* 7110 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 7113 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 7126
/* 7117 */    MCD::OPC_CheckPredicate, 7, 88, 25, // Skip to: 13609
/* 7121 */    MCD::OPC_Decode, 188, 9, 132, 1, // Opcode: MULV_B
/* 7126 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 7139
/* 7130 */    MCD::OPC_CheckPredicate, 7, 75, 25, // Skip to: 13609
/* 7134 */    MCD::OPC_Decode, 190, 9, 133, 1, // Opcode: MULV_H
/* 7139 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 7152
/* 7143 */    MCD::OPC_CheckPredicate, 7, 62, 25, // Skip to: 13609
/* 7147 */    MCD::OPC_Decode, 191, 9, 134, 1, // Opcode: MULV_W
/* 7152 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 7165
/* 7156 */    MCD::OPC_CheckPredicate, 7, 49, 25, // Skip to: 13609
/* 7160 */    MCD::OPC_Decode, 189, 9, 135, 1, // Opcode: MULV_D
/* 7165 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 7178
/* 7169 */    MCD::OPC_CheckPredicate, 7, 36, 25, // Skip to: 13609
/* 7173 */    MCD::OPC_Decode, 242, 7, 136, 1, // Opcode: MADDV_B
/* 7178 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 7191
/* 7182 */    MCD::OPC_CheckPredicate, 7, 23, 25, // Skip to: 13609
/* 7186 */    MCD::OPC_Decode, 244, 7, 137, 1, // Opcode: MADDV_H
/* 7191 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 7204
/* 7195 */    MCD::OPC_CheckPredicate, 7, 10, 25, // Skip to: 13609
/* 7199 */    MCD::OPC_Decode, 245, 7, 138, 1, // Opcode: MADDV_W
/* 7204 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 7217
/* 7208 */    MCD::OPC_CheckPredicate, 7, 253, 24, // Skip to: 13609
/* 7212 */    MCD::OPC_Decode, 243, 7, 139, 1, // Opcode: MADDV_D
/* 7217 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 7230
/* 7221 */    MCD::OPC_CheckPredicate, 7, 240, 24, // Skip to: 13609
/* 7225 */    MCD::OPC_Decode, 131, 9, 136, 1, // Opcode: MSUBV_B
/* 7230 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 7243
/* 7234 */    MCD::OPC_CheckPredicate, 7, 227, 24, // Skip to: 13609
/* 7238 */    MCD::OPC_Decode, 133, 9, 137, 1, // Opcode: MSUBV_H
/* 7243 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 7256
/* 7247 */    MCD::OPC_CheckPredicate, 7, 214, 24, // Skip to: 13609
/* 7251 */    MCD::OPC_Decode, 134, 9, 138, 1, // Opcode: MSUBV_W
/* 7256 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 7269
/* 7260 */    MCD::OPC_CheckPredicate, 7, 201, 24, // Skip to: 13609
/* 7264 */    MCD::OPC_Decode, 132, 9, 139, 1, // Opcode: MSUBV_D
/* 7269 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 7282
/* 7273 */    MCD::OPC_CheckPredicate, 7, 188, 24, // Skip to: 13609
/* 7277 */    MCD::OPC_Decode, 166, 4, 132, 1, // Opcode: DIV_S_B
/* 7282 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 7295
/* 7286 */    MCD::OPC_CheckPredicate, 7, 175, 24, // Skip to: 13609
/* 7290 */    MCD::OPC_Decode, 168, 4, 133, 1, // Opcode: DIV_S_H
/* 7295 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 7308
/* 7299 */    MCD::OPC_CheckPredicate, 7, 162, 24, // Skip to: 13609
/* 7303 */    MCD::OPC_Decode, 169, 4, 134, 1, // Opcode: DIV_S_W
/* 7308 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 7321
/* 7312 */    MCD::OPC_CheckPredicate, 7, 149, 24, // Skip to: 13609
/* 7316 */    MCD::OPC_Decode, 167, 4, 135, 1, // Opcode: DIV_S_D
/* 7321 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 7334
/* 7325 */    MCD::OPC_CheckPredicate, 7, 136, 24, // Skip to: 13609
/* 7329 */    MCD::OPC_Decode, 170, 4, 132, 1, // Opcode: DIV_U_B
/* 7334 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 7347
/* 7338 */    MCD::OPC_CheckPredicate, 7, 123, 24, // Skip to: 13609
/* 7342 */    MCD::OPC_Decode, 172, 4, 133, 1, // Opcode: DIV_U_H
/* 7347 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 7360
/* 7351 */    MCD::OPC_CheckPredicate, 7, 110, 24, // Skip to: 13609
/* 7355 */    MCD::OPC_Decode, 173, 4, 134, 1, // Opcode: DIV_U_W
/* 7360 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 7373
/* 7364 */    MCD::OPC_CheckPredicate, 7, 97, 24, // Skip to: 13609
/* 7368 */    MCD::OPC_Decode, 171, 4, 135, 1, // Opcode: DIV_U_D
/* 7373 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 7386
/* 7377 */    MCD::OPC_CheckPredicate, 7, 84, 24, // Skip to: 13609
/* 7381 */    MCD::OPC_Decode, 201, 8, 132, 1, // Opcode: MOD_S_B
/* 7386 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 7399
/* 7390 */    MCD::OPC_CheckPredicate, 7, 71, 24, // Skip to: 13609
/* 7394 */    MCD::OPC_Decode, 203, 8, 133, 1, // Opcode: MOD_S_H
/* 7399 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 7412
/* 7403 */    MCD::OPC_CheckPredicate, 7, 58, 24, // Skip to: 13609
/* 7407 */    MCD::OPC_Decode, 204, 8, 134, 1, // Opcode: MOD_S_W
/* 7412 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 7425
/* 7416 */    MCD::OPC_CheckPredicate, 7, 45, 24, // Skip to: 13609
/* 7420 */    MCD::OPC_Decode, 202, 8, 135, 1, // Opcode: MOD_S_D
/* 7425 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 7438
/* 7429 */    MCD::OPC_CheckPredicate, 7, 32, 24, // Skip to: 13609
/* 7433 */    MCD::OPC_Decode, 205, 8, 132, 1, // Opcode: MOD_U_B
/* 7438 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 7451
/* 7442 */    MCD::OPC_CheckPredicate, 7, 19, 24, // Skip to: 13609
/* 7446 */    MCD::OPC_Decode, 207, 8, 133, 1, // Opcode: MOD_U_H
/* 7451 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 7464
/* 7455 */    MCD::OPC_CheckPredicate, 7, 6, 24, // Skip to: 13609
/* 7459 */    MCD::OPC_Decode, 208, 8, 134, 1, // Opcode: MOD_U_W
/* 7464 */    MCD::OPC_FilterValue, 31, 253, 23, // Skip to: 13609
/* 7468 */    MCD::OPC_CheckPredicate, 7, 249, 23, // Skip to: 13609
/* 7472 */    MCD::OPC_Decode, 206, 8, 135, 1, // Opcode: MOD_U_D
/* 7477 */    MCD::OPC_FilterValue, 19, 237, 0, // Skip to: 7718
/* 7481 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 7484 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 7497
/* 7488 */    MCD::OPC_CheckPredicate, 7, 229, 23, // Skip to: 13609
/* 7492 */    MCD::OPC_Decode, 193, 4, 140, 1, // Opcode: DOTP_S_H
/* 7497 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 7510
/* 7501 */    MCD::OPC_CheckPredicate, 7, 216, 23, // Skip to: 13609
/* 7505 */    MCD::OPC_Decode, 194, 4, 141, 1, // Opcode: DOTP_S_W
/* 7510 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 7523
/* 7514 */    MCD::OPC_CheckPredicate, 7, 203, 23, // Skip to: 13609
/* 7518 */    MCD::OPC_Decode, 192, 4, 142, 1, // Opcode: DOTP_S_D
/* 7523 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 7536
/* 7527 */    MCD::OPC_CheckPredicate, 7, 190, 23, // Skip to: 13609
/* 7531 */    MCD::OPC_Decode, 196, 4, 140, 1, // Opcode: DOTP_U_H
/* 7536 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 7549
/* 7540 */    MCD::OPC_CheckPredicate, 7, 177, 23, // Skip to: 13609
/* 7544 */    MCD::OPC_Decode, 197, 4, 141, 1, // Opcode: DOTP_U_W
/* 7549 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 7562
/* 7553 */    MCD::OPC_CheckPredicate, 7, 164, 23, // Skip to: 13609
/* 7557 */    MCD::OPC_Decode, 195, 4, 142, 1, // Opcode: DOTP_U_D
/* 7562 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 7575
/* 7566 */    MCD::OPC_CheckPredicate, 7, 151, 23, // Skip to: 13609
/* 7570 */    MCD::OPC_Decode, 199, 4, 143, 1, // Opcode: DPADD_S_H
/* 7575 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 7588
/* 7579 */    MCD::OPC_CheckPredicate, 7, 138, 23, // Skip to: 13609
/* 7583 */    MCD::OPC_Decode, 200, 4, 144, 1, // Opcode: DPADD_S_W
/* 7588 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 7601
/* 7592 */    MCD::OPC_CheckPredicate, 7, 125, 23, // Skip to: 13609
/* 7596 */    MCD::OPC_Decode, 198, 4, 145, 1, // Opcode: DPADD_S_D
/* 7601 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 7614
/* 7605 */    MCD::OPC_CheckPredicate, 7, 112, 23, // Skip to: 13609
/* 7609 */    MCD::OPC_Decode, 202, 4, 143, 1, // Opcode: DPADD_U_H
/* 7614 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 7627
/* 7618 */    MCD::OPC_CheckPredicate, 7, 99, 23, // Skip to: 13609
/* 7622 */    MCD::OPC_Decode, 203, 4, 144, 1, // Opcode: DPADD_U_W
/* 7627 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 7640
/* 7631 */    MCD::OPC_CheckPredicate, 7, 86, 23, // Skip to: 13609
/* 7635 */    MCD::OPC_Decode, 201, 4, 145, 1, // Opcode: DPADD_U_D
/* 7640 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 7653
/* 7644 */    MCD::OPC_CheckPredicate, 7, 73, 23, // Skip to: 13609
/* 7648 */    MCD::OPC_Decode, 218, 4, 143, 1, // Opcode: DPSUB_S_H
/* 7653 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 7666
/* 7657 */    MCD::OPC_CheckPredicate, 7, 60, 23, // Skip to: 13609
/* 7661 */    MCD::OPC_Decode, 219, 4, 144, 1, // Opcode: DPSUB_S_W
/* 7666 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 7679
/* 7670 */    MCD::OPC_CheckPredicate, 7, 47, 23, // Skip to: 13609
/* 7674 */    MCD::OPC_Decode, 217, 4, 145, 1, // Opcode: DPSUB_S_D
/* 7679 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 7692
/* 7683 */    MCD::OPC_CheckPredicate, 7, 34, 23, // Skip to: 13609
/* 7687 */    MCD::OPC_Decode, 221, 4, 143, 1, // Opcode: DPSUB_U_H
/* 7692 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 7705
/* 7696 */    MCD::OPC_CheckPredicate, 7, 21, 23, // Skip to: 13609
/* 7700 */    MCD::OPC_Decode, 222, 4, 144, 1, // Opcode: DPSUB_U_W
/* 7705 */    MCD::OPC_FilterValue, 23, 12, 23, // Skip to: 13609
/* 7709 */    MCD::OPC_CheckPredicate, 7, 8, 23, // Skip to: 13609
/* 7713 */    MCD::OPC_Decode, 220, 4, 145, 1, // Opcode: DPSUB_U_D
/* 7718 */    MCD::OPC_FilterValue, 20, 163, 1, // Skip to: 8141
/* 7722 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 7725 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 7738
/* 7729 */    MCD::OPC_CheckPredicate, 7, 244, 22, // Skip to: 13609
/* 7733 */    MCD::OPC_Decode, 196, 11, 146, 1, // Opcode: SLD_B
/* 7738 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 7751
/* 7742 */    MCD::OPC_CheckPredicate, 7, 231, 22, // Skip to: 13609
/* 7746 */    MCD::OPC_Decode, 198, 11, 147, 1, // Opcode: SLD_H
/* 7751 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 7764
/* 7755 */    MCD::OPC_CheckPredicate, 7, 218, 22, // Skip to: 13609
/* 7759 */    MCD::OPC_Decode, 199, 11, 148, 1, // Opcode: SLD_W
/* 7764 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 7777
/* 7768 */    MCD::OPC_CheckPredicate, 7, 205, 22, // Skip to: 13609
/* 7772 */    MCD::OPC_Decode, 197, 11, 149, 1, // Opcode: SLD_D
/* 7777 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 7790
/* 7781 */    MCD::OPC_CheckPredicate, 7, 192, 22, // Skip to: 13609
/* 7785 */    MCD::OPC_Decode, 238, 11, 150, 1, // Opcode: SPLAT_B
/* 7790 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 7803
/* 7794 */    MCD::OPC_CheckPredicate, 7, 179, 22, // Skip to: 13609
/* 7798 */    MCD::OPC_Decode, 240, 11, 151, 1, // Opcode: SPLAT_H
/* 7803 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 7816
/* 7807 */    MCD::OPC_CheckPredicate, 7, 166, 22, // Skip to: 13609
/* 7811 */    MCD::OPC_Decode, 241, 11, 152, 1, // Opcode: SPLAT_W
/* 7816 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 7829
/* 7820 */    MCD::OPC_CheckPredicate, 7, 153, 22, // Skip to: 13609
/* 7824 */    MCD::OPC_Decode, 239, 11, 153, 1, // Opcode: SPLAT_D
/* 7829 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 7842
/* 7833 */    MCD::OPC_CheckPredicate, 7, 140, 22, // Skip to: 13609
/* 7837 */    MCD::OPC_Decode, 252, 9, 132, 1, // Opcode: PCKEV_B
/* 7842 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 7855
/* 7846 */    MCD::OPC_CheckPredicate, 7, 127, 22, // Skip to: 13609
/* 7850 */    MCD::OPC_Decode, 254, 9, 133, 1, // Opcode: PCKEV_H
/* 7855 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 7868
/* 7859 */    MCD::OPC_CheckPredicate, 7, 114, 22, // Skip to: 13609
/* 7863 */    MCD::OPC_Decode, 255, 9, 134, 1, // Opcode: PCKEV_W
/* 7868 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 7881
/* 7872 */    MCD::OPC_CheckPredicate, 7, 101, 22, // Skip to: 13609
/* 7876 */    MCD::OPC_Decode, 253, 9, 135, 1, // Opcode: PCKEV_D
/* 7881 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 7894
/* 7885 */    MCD::OPC_CheckPredicate, 7, 88, 22, // Skip to: 13609
/* 7889 */    MCD::OPC_Decode, 128, 10, 132, 1, // Opcode: PCKOD_B
/* 7894 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 7907
/* 7898 */    MCD::OPC_CheckPredicate, 7, 75, 22, // Skip to: 13609
/* 7902 */    MCD::OPC_Decode, 130, 10, 133, 1, // Opcode: PCKOD_H
/* 7907 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 7920
/* 7911 */    MCD::OPC_CheckPredicate, 7, 62, 22, // Skip to: 13609
/* 7915 */    MCD::OPC_Decode, 131, 10, 134, 1, // Opcode: PCKOD_W
/* 7920 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 7933
/* 7924 */    MCD::OPC_CheckPredicate, 7, 49, 22, // Skip to: 13609
/* 7928 */    MCD::OPC_Decode, 129, 10, 135, 1, // Opcode: PCKOD_D
/* 7933 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 7946
/* 7937 */    MCD::OPC_CheckPredicate, 7, 36, 22, // Skip to: 13609
/* 7941 */    MCD::OPC_Decode, 197, 6, 132, 1, // Opcode: ILVL_B
/* 7946 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 7959
/* 7950 */    MCD::OPC_CheckPredicate, 7, 23, 22, // Skip to: 13609
/* 7954 */    MCD::OPC_Decode, 199, 6, 133, 1, // Opcode: ILVL_H
/* 7959 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 7972
/* 7963 */    MCD::OPC_CheckPredicate, 7, 10, 22, // Skip to: 13609
/* 7967 */    MCD::OPC_Decode, 200, 6, 134, 1, // Opcode: ILVL_W
/* 7972 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 7985
/* 7976 */    MCD::OPC_CheckPredicate, 7, 253, 21, // Skip to: 13609
/* 7980 */    MCD::OPC_Decode, 198, 6, 135, 1, // Opcode: ILVL_D
/* 7985 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 7998
/* 7989 */    MCD::OPC_CheckPredicate, 7, 240, 21, // Skip to: 13609
/* 7993 */    MCD::OPC_Decode, 205, 6, 132, 1, // Opcode: ILVR_B
/* 7998 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 8011
/* 8002 */    MCD::OPC_CheckPredicate, 7, 227, 21, // Skip to: 13609
/* 8006 */    MCD::OPC_Decode, 207, 6, 133, 1, // Opcode: ILVR_H
/* 8011 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 8024
/* 8015 */    MCD::OPC_CheckPredicate, 7, 214, 21, // Skip to: 13609
/* 8019 */    MCD::OPC_Decode, 208, 6, 134, 1, // Opcode: ILVR_W
/* 8024 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 8037
/* 8028 */    MCD::OPC_CheckPredicate, 7, 201, 21, // Skip to: 13609
/* 8032 */    MCD::OPC_Decode, 206, 6, 135, 1, // Opcode: ILVR_D
/* 8037 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 8050
/* 8041 */    MCD::OPC_CheckPredicate, 7, 188, 21, // Skip to: 13609
/* 8045 */    MCD::OPC_Decode, 193, 6, 132, 1, // Opcode: ILVEV_B
/* 8050 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 8063
/* 8054 */    MCD::OPC_CheckPredicate, 7, 175, 21, // Skip to: 13609
/* 8058 */    MCD::OPC_Decode, 195, 6, 133, 1, // Opcode: ILVEV_H
/* 8063 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 8076
/* 8067 */    MCD::OPC_CheckPredicate, 7, 162, 21, // Skip to: 13609
/* 8071 */    MCD::OPC_Decode, 196, 6, 134, 1, // Opcode: ILVEV_W
/* 8076 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 8089
/* 8080 */    MCD::OPC_CheckPredicate, 7, 149, 21, // Skip to: 13609
/* 8084 */    MCD::OPC_Decode, 194, 6, 135, 1, // Opcode: ILVEV_D
/* 8089 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 8102
/* 8093 */    MCD::OPC_CheckPredicate, 7, 136, 21, // Skip to: 13609
/* 8097 */    MCD::OPC_Decode, 201, 6, 132, 1, // Opcode: ILVOD_B
/* 8102 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 8115
/* 8106 */    MCD::OPC_CheckPredicate, 7, 123, 21, // Skip to: 13609
/* 8110 */    MCD::OPC_Decode, 203, 6, 133, 1, // Opcode: ILVOD_H
/* 8115 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 8128
/* 8119 */    MCD::OPC_CheckPredicate, 7, 110, 21, // Skip to: 13609
/* 8123 */    MCD::OPC_Decode, 204, 6, 134, 1, // Opcode: ILVOD_W
/* 8128 */    MCD::OPC_FilterValue, 31, 101, 21, // Skip to: 13609
/* 8132 */    MCD::OPC_CheckPredicate, 7, 97, 21, // Skip to: 13609
/* 8136 */    MCD::OPC_Decode, 202, 6, 135, 1, // Opcode: ILVOD_D
/* 8141 */    MCD::OPC_FilterValue, 21, 59, 1, // Skip to: 8460
/* 8145 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 8148 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8161
/* 8152 */    MCD::OPC_CheckPredicate, 7, 77, 21, // Skip to: 13609
/* 8156 */    MCD::OPC_Decode, 201, 13, 136, 1, // Opcode: VSHF_B
/* 8161 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 8174
/* 8165 */    MCD::OPC_CheckPredicate, 7, 64, 21, // Skip to: 13609
/* 8169 */    MCD::OPC_Decode, 203, 13, 137, 1, // Opcode: VSHF_H
/* 8174 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 8187
/* 8178 */    MCD::OPC_CheckPredicate, 7, 51, 21, // Skip to: 13609
/* 8182 */    MCD::OPC_Decode, 204, 13, 138, 1, // Opcode: VSHF_W
/* 8187 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 8200
/* 8191 */    MCD::OPC_CheckPredicate, 7, 38, 21, // Skip to: 13609
/* 8195 */    MCD::OPC_Decode, 202, 13, 139, 1, // Opcode: VSHF_D
/* 8200 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 8213
/* 8204 */    MCD::OPC_CheckPredicate, 7, 25, 21, // Skip to: 13609
/* 8208 */    MCD::OPC_Decode, 251, 11, 132, 1, // Opcode: SRAR_B
/* 8213 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 8226
/* 8217 */    MCD::OPC_CheckPredicate, 7, 12, 21, // Skip to: 13609
/* 8221 */    MCD::OPC_Decode, 253, 11, 133, 1, // Opcode: SRAR_H
/* 8226 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 8239
/* 8230 */    MCD::OPC_CheckPredicate, 7, 255, 20, // Skip to: 13609
/* 8234 */    MCD::OPC_Decode, 254, 11, 134, 1, // Opcode: SRAR_W
/* 8239 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 8252
/* 8243 */    MCD::OPC_CheckPredicate, 7, 242, 20, // Skip to: 13609
/* 8247 */    MCD::OPC_Decode, 252, 11, 135, 1, // Opcode: SRAR_D
/* 8252 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 8265
/* 8256 */    MCD::OPC_CheckPredicate, 7, 229, 20, // Skip to: 13609
/* 8260 */    MCD::OPC_Decode, 144, 12, 132, 1, // Opcode: SRLR_B
/* 8265 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 8278
/* 8269 */    MCD::OPC_CheckPredicate, 7, 216, 20, // Skip to: 13609
/* 8273 */    MCD::OPC_Decode, 146, 12, 133, 1, // Opcode: SRLR_H
/* 8278 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 8291
/* 8282 */    MCD::OPC_CheckPredicate, 7, 203, 20, // Skip to: 13609
/* 8286 */    MCD::OPC_Decode, 147, 12, 134, 1, // Opcode: SRLR_W
/* 8291 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 8304
/* 8295 */    MCD::OPC_CheckPredicate, 7, 190, 20, // Skip to: 13609
/* 8299 */    MCD::OPC_Decode, 145, 12, 135, 1, // Opcode: SRLR_D
/* 8304 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 8317
/* 8308 */    MCD::OPC_CheckPredicate, 7, 177, 20, // Skip to: 13609
/* 8312 */    MCD::OPC_Decode, 182, 6, 140, 1, // Opcode: HADD_S_H
/* 8317 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 8330
/* 8321 */    MCD::OPC_CheckPredicate, 7, 164, 20, // Skip to: 13609
/* 8325 */    MCD::OPC_Decode, 183, 6, 141, 1, // Opcode: HADD_S_W
/* 8330 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 8343
/* 8334 */    MCD::OPC_CheckPredicate, 7, 151, 20, // Skip to: 13609
/* 8338 */    MCD::OPC_Decode, 181, 6, 142, 1, // Opcode: HADD_S_D
/* 8343 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 8356
/* 8347 */    MCD::OPC_CheckPredicate, 7, 138, 20, // Skip to: 13609
/* 8351 */    MCD::OPC_Decode, 185, 6, 140, 1, // Opcode: HADD_U_H
/* 8356 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 8369
/* 8360 */    MCD::OPC_CheckPredicate, 7, 125, 20, // Skip to: 13609
/* 8364 */    MCD::OPC_Decode, 186, 6, 141, 1, // Opcode: HADD_U_W
/* 8369 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 8382
/* 8373 */    MCD::OPC_CheckPredicate, 7, 112, 20, // Skip to: 13609
/* 8377 */    MCD::OPC_Decode, 184, 6, 142, 1, // Opcode: HADD_U_D
/* 8382 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 8395
/* 8386 */    MCD::OPC_CheckPredicate, 7, 99, 20, // Skip to: 13609
/* 8390 */    MCD::OPC_Decode, 188, 6, 140, 1, // Opcode: HSUB_S_H
/* 8395 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 8408
/* 8399 */    MCD::OPC_CheckPredicate, 7, 86, 20, // Skip to: 13609
/* 8403 */    MCD::OPC_Decode, 189, 6, 141, 1, // Opcode: HSUB_S_W
/* 8408 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 8421
/* 8412 */    MCD::OPC_CheckPredicate, 7, 73, 20, // Skip to: 13609
/* 8416 */    MCD::OPC_Decode, 187, 6, 142, 1, // Opcode: HSUB_S_D
/* 8421 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 8434
/* 8425 */    MCD::OPC_CheckPredicate, 7, 60, 20, // Skip to: 13609
/* 8429 */    MCD::OPC_Decode, 191, 6, 140, 1, // Opcode: HSUB_U_H
/* 8434 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 8447
/* 8438 */    MCD::OPC_CheckPredicate, 7, 47, 20, // Skip to: 13609
/* 8442 */    MCD::OPC_Decode, 192, 6, 141, 1, // Opcode: HSUB_U_W
/* 8447 */    MCD::OPC_FilterValue, 31, 38, 20, // Skip to: 13609
/* 8451 */    MCD::OPC_CheckPredicate, 7, 34, 20, // Skip to: 13609
/* 8455 */    MCD::OPC_Decode, 190, 6, 142, 1, // Opcode: HSUB_U_D
/* 8460 */    MCD::OPC_FilterValue, 25, 230, 1, // Skip to: 8950
/* 8464 */    MCD::OPC_ExtractField, 20, 6,  // Inst{25-20} ...
/* 8467 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8480
/* 8471 */    MCD::OPC_CheckPredicate, 7, 14, 20, // Skip to: 13609
/* 8475 */    MCD::OPC_Decode, 192, 11, 154, 1, // Opcode: SLDI_B
/* 8480 */    MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 8499
/* 8484 */    MCD::OPC_CheckPredicate, 7, 1, 20, // Skip to: 13609
/* 8488 */    MCD::OPC_CheckField, 19, 1, 0, 251, 19, // Skip to: 13609
/* 8494 */    MCD::OPC_Decode, 194, 11, 155, 1, // Opcode: SLDI_H
/* 8499 */    MCD::OPC_FilterValue, 3, 54, 0, // Skip to: 8557
/* 8503 */    MCD::OPC_ExtractField, 18, 2,  // Inst{19-18} ...
/* 8506 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8519
/* 8510 */    MCD::OPC_CheckPredicate, 7, 231, 19, // Skip to: 13609
/* 8514 */    MCD::OPC_Decode, 195, 11, 156, 1, // Opcode: SLDI_W
/* 8519 */    MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 8538
/* 8523 */    MCD::OPC_CheckPredicate, 7, 218, 19, // Skip to: 13609
/* 8527 */    MCD::OPC_CheckField, 17, 1, 0, 212, 19, // Skip to: 13609
/* 8533 */    MCD::OPC_Decode, 193, 11, 157, 1, // Opcode: SLDI_D
/* 8538 */    MCD::OPC_FilterValue, 3, 203, 19, // Skip to: 13609
/* 8542 */    MCD::OPC_CheckPredicate, 7, 199, 19, // Skip to: 13609
/* 8546 */    MCD::OPC_CheckField, 16, 2, 2, 193, 19, // Skip to: 13609
/* 8552 */    MCD::OPC_Decode, 193, 3, 158, 1, // Opcode: CTCMSA
/* 8557 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 8570
/* 8561 */    MCD::OPC_CheckPredicate, 7, 180, 19, // Skip to: 13609
/* 8565 */    MCD::OPC_Decode, 234, 11, 159, 1, // Opcode: SPLATI_B
/* 8570 */    MCD::OPC_FilterValue, 6, 15, 0, // Skip to: 8589
/* 8574 */    MCD::OPC_CheckPredicate, 7, 167, 19, // Skip to: 13609
/* 8578 */    MCD::OPC_CheckField, 19, 1, 0, 161, 19, // Skip to: 13609
/* 8584 */    MCD::OPC_Decode, 236, 11, 160, 1, // Opcode: SPLATI_H
/* 8589 */    MCD::OPC_FilterValue, 7, 54, 0, // Skip to: 8647
/* 8593 */    MCD::OPC_ExtractField, 18, 2,  // Inst{19-18} ...
/* 8596 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8609
/* 8600 */    MCD::OPC_CheckPredicate, 7, 141, 19, // Skip to: 13609
/* 8604 */    MCD::OPC_Decode, 237, 11, 161, 1, // Opcode: SPLATI_W
/* 8609 */    MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 8628
/* 8613 */    MCD::OPC_CheckPredicate, 7, 128, 19, // Skip to: 13609
/* 8617 */    MCD::OPC_CheckField, 17, 1, 0, 122, 19, // Skip to: 13609
/* 8623 */    MCD::OPC_Decode, 235, 11, 162, 1, // Opcode: SPLATI_D
/* 8628 */    MCD::OPC_FilterValue, 3, 113, 19, // Skip to: 13609
/* 8632 */    MCD::OPC_CheckPredicate, 7, 109, 19, // Skip to: 13609
/* 8636 */    MCD::OPC_CheckField, 16, 2, 2, 103, 19, // Skip to: 13609
/* 8642 */    MCD::OPC_Decode, 221, 2, 163, 1, // Opcode: CFCMSA
/* 8647 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 8660
/* 8651 */    MCD::OPC_CheckPredicate, 7, 90, 19, // Skip to: 13609
/* 8655 */    MCD::OPC_Decode, 183, 3, 164, 1, // Opcode: COPY_S_B
/* 8660 */    MCD::OPC_FilterValue, 10, 15, 0, // Skip to: 8679
/* 8664 */    MCD::OPC_CheckPredicate, 7, 77, 19, // Skip to: 13609
/* 8668 */    MCD::OPC_CheckField, 19, 1, 0, 71, 19, // Skip to: 13609
/* 8674 */    MCD::OPC_Decode, 185, 3, 165, 1, // Opcode: COPY_S_H
/* 8679 */    MCD::OPC_FilterValue, 11, 54, 0, // Skip to: 8737
/* 8683 */    MCD::OPC_ExtractField, 18, 2,  // Inst{19-18} ...
/* 8686 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8699
/* 8690 */    MCD::OPC_CheckPredicate, 7, 51, 19, // Skip to: 13609
/* 8694 */    MCD::OPC_Decode, 186, 3, 166, 1, // Opcode: COPY_S_W
/* 8699 */    MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 8718
/* 8703 */    MCD::OPC_CheckPredicate, 13, 38, 19, // Skip to: 13609
/* 8707 */    MCD::OPC_CheckField, 17, 1, 0, 32, 19, // Skip to: 13609
/* 8713 */    MCD::OPC_Decode, 184, 3, 167, 1, // Opcode: COPY_S_D
/* 8718 */    MCD::OPC_FilterValue, 3, 23, 19, // Skip to: 13609
/* 8722 */    MCD::OPC_CheckPredicate, 7, 19, 19, // Skip to: 13609
/* 8726 */    MCD::OPC_CheckField, 16, 2, 2, 13, 19, // Skip to: 13609
/* 8732 */    MCD::OPC_Decode, 210, 8, 168, 1, // Opcode: MOVE_V
/* 8737 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 8750
/* 8741 */    MCD::OPC_CheckPredicate, 7, 0, 19, // Skip to: 13609
/* 8745 */    MCD::OPC_Decode, 187, 3, 164, 1, // Opcode: COPY_U_B
/* 8750 */    MCD::OPC_FilterValue, 14, 15, 0, // Skip to: 8769
/* 8754 */    MCD::OPC_CheckPredicate, 7, 243, 18, // Skip to: 13609
/* 8758 */    MCD::OPC_CheckField, 19, 1, 0, 237, 18, // Skip to: 13609
/* 8764 */    MCD::OPC_Decode, 189, 3, 165, 1, // Opcode: COPY_U_H
/* 8769 */    MCD::OPC_FilterValue, 15, 35, 0, // Skip to: 8808
/* 8773 */    MCD::OPC_ExtractField, 18, 2,  // Inst{19-18} ...
/* 8776 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8789
/* 8780 */    MCD::OPC_CheckPredicate, 7, 217, 18, // Skip to: 13609
/* 8784 */    MCD::OPC_Decode, 190, 3, 166, 1, // Opcode: COPY_U_W
/* 8789 */    MCD::OPC_FilterValue, 2, 208, 18, // Skip to: 13609
/* 8793 */    MCD::OPC_CheckPredicate, 13, 204, 18, // Skip to: 13609
/* 8797 */    MCD::OPC_CheckField, 17, 1, 0, 198, 18, // Skip to: 13609
/* 8803 */    MCD::OPC_Decode, 188, 3, 167, 1, // Opcode: COPY_U_D
/* 8808 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 8821
/* 8812 */    MCD::OPC_CheckPredicate, 7, 185, 18, // Skip to: 13609
/* 8816 */    MCD::OPC_Decode, 210, 6, 169, 1, // Opcode: INSERT_B
/* 8821 */    MCD::OPC_FilterValue, 18, 15, 0, // Skip to: 8840
/* 8825 */    MCD::OPC_CheckPredicate, 7, 172, 18, // Skip to: 13609
/* 8829 */    MCD::OPC_CheckField, 19, 1, 0, 166, 18, // Skip to: 13609
/* 8835 */    MCD::OPC_Decode, 218, 6, 170, 1, // Opcode: INSERT_H
/* 8840 */    MCD::OPC_FilterValue, 19, 35, 0, // Skip to: 8879
/* 8844 */    MCD::OPC_ExtractField, 18, 2,  // Inst{19-18} ...
/* 8847 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8860
/* 8851 */    MCD::OPC_CheckPredicate, 7, 146, 18, // Skip to: 13609
/* 8855 */    MCD::OPC_Decode, 220, 6, 171, 1, // Opcode: INSERT_W
/* 8860 */    MCD::OPC_FilterValue, 2, 137, 18, // Skip to: 13609
/* 8864 */    MCD::OPC_CheckPredicate, 13, 133, 18, // Skip to: 13609
/* 8868 */    MCD::OPC_CheckField, 17, 1, 0, 127, 18, // Skip to: 13609
/* 8874 */    MCD::OPC_Decode, 212, 6, 172, 1, // Opcode: INSERT_D
/* 8879 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 8892
/* 8883 */    MCD::OPC_CheckPredicate, 7, 114, 18, // Skip to: 13609
/* 8887 */    MCD::OPC_Decode, 223, 6, 173, 1, // Opcode: INSVE_B
/* 8892 */    MCD::OPC_FilterValue, 22, 15, 0, // Skip to: 8911
/* 8896 */    MCD::OPC_CheckPredicate, 7, 101, 18, // Skip to: 13609
/* 8900 */    MCD::OPC_CheckField, 19, 1, 0, 95, 18, // Skip to: 13609
/* 8906 */    MCD::OPC_Decode, 225, 6, 173, 1, // Opcode: INSVE_H
/* 8911 */    MCD::OPC_FilterValue, 23, 86, 18, // Skip to: 13609
/* 8915 */    MCD::OPC_ExtractField, 18, 2,  // Inst{19-18} ...
/* 8918 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8931
/* 8922 */    MCD::OPC_CheckPredicate, 7, 75, 18, // Skip to: 13609
/* 8926 */    MCD::OPC_Decode, 226, 6, 173, 1, // Opcode: INSVE_W
/* 8931 */    MCD::OPC_FilterValue, 2, 66, 18, // Skip to: 13609
/* 8935 */    MCD::OPC_CheckPredicate, 7, 62, 18, // Skip to: 13609
/* 8939 */    MCD::OPC_CheckField, 17, 1, 0, 56, 18, // Skip to: 13609
/* 8945 */    MCD::OPC_Decode, 224, 6, 173, 1, // Opcode: INSVE_D
/* 8950 */    MCD::OPC_FilterValue, 26, 163, 1, // Skip to: 9373
/* 8954 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 8957 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 8970
/* 8961 */    MCD::OPC_CheckPredicate, 7, 36, 18, // Skip to: 13609
/* 8965 */    MCD::OPC_Decode, 159, 5, 134, 1, // Opcode: FCAF_W
/* 8970 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 8983
/* 8974 */    MCD::OPC_CheckPredicate, 7, 23, 18, // Skip to: 13609
/* 8978 */    MCD::OPC_Decode, 158, 5, 135, 1, // Opcode: FCAF_D
/* 8983 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 8996
/* 8987 */    MCD::OPC_CheckPredicate, 7, 10, 18, // Skip to: 13609
/* 8991 */    MCD::OPC_Decode, 186, 5, 134, 1, // Opcode: FCUN_W
/* 8996 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 9009
/* 9000 */    MCD::OPC_CheckPredicate, 7, 253, 17, // Skip to: 13609
/* 9004 */    MCD::OPC_Decode, 185, 5, 135, 1, // Opcode: FCUN_D
/* 9009 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 9022
/* 9013 */    MCD::OPC_CheckPredicate, 7, 240, 17, // Skip to: 13609
/* 9017 */    MCD::OPC_Decode, 161, 5, 134, 1, // Opcode: FCEQ_W
/* 9022 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 9035
/* 9026 */    MCD::OPC_CheckPredicate, 7, 227, 17, // Skip to: 13609
/* 9030 */    MCD::OPC_Decode, 160, 5, 135, 1, // Opcode: FCEQ_D
/* 9035 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 9048
/* 9039 */    MCD::OPC_CheckPredicate, 7, 214, 17, // Skip to: 13609
/* 9043 */    MCD::OPC_Decode, 178, 5, 134, 1, // Opcode: FCUEQ_W
/* 9048 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 9061
/* 9052 */    MCD::OPC_CheckPredicate, 7, 201, 17, // Skip to: 13609
/* 9056 */    MCD::OPC_Decode, 177, 5, 135, 1, // Opcode: FCUEQ_D
/* 9061 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 9074
/* 9065 */    MCD::OPC_CheckPredicate, 7, 188, 17, // Skip to: 13609
/* 9069 */    MCD::OPC_Decode, 167, 5, 134, 1, // Opcode: FCLT_W
/* 9074 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 9087
/* 9078 */    MCD::OPC_CheckPredicate, 7, 175, 17, // Skip to: 13609
/* 9082 */    MCD::OPC_Decode, 166, 5, 135, 1, // Opcode: FCLT_D
/* 9087 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 9100
/* 9091 */    MCD::OPC_CheckPredicate, 7, 162, 17, // Skip to: 13609
/* 9095 */    MCD::OPC_Decode, 182, 5, 134, 1, // Opcode: FCULT_W
/* 9100 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 9113
/* 9104 */    MCD::OPC_CheckPredicate, 7, 149, 17, // Skip to: 13609
/* 9108 */    MCD::OPC_Decode, 181, 5, 135, 1, // Opcode: FCULT_D
/* 9113 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 9126
/* 9117 */    MCD::OPC_CheckPredicate, 7, 136, 17, // Skip to: 13609
/* 9121 */    MCD::OPC_Decode, 165, 5, 134, 1, // Opcode: FCLE_W
/* 9126 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 9139
/* 9130 */    MCD::OPC_CheckPredicate, 7, 123, 17, // Skip to: 13609
/* 9134 */    MCD::OPC_Decode, 164, 5, 135, 1, // Opcode: FCLE_D
/* 9139 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 9152
/* 9143 */    MCD::OPC_CheckPredicate, 7, 110, 17, // Skip to: 13609
/* 9147 */    MCD::OPC_Decode, 180, 5, 134, 1, // Opcode: FCULE_W
/* 9152 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 9165
/* 9156 */    MCD::OPC_CheckPredicate, 7, 97, 17, // Skip to: 13609
/* 9160 */    MCD::OPC_Decode, 179, 5, 135, 1, // Opcode: FCULE_D
/* 9165 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 9178
/* 9169 */    MCD::OPC_CheckPredicate, 7, 84, 17, // Skip to: 13609
/* 9173 */    MCD::OPC_Decode, 135, 6, 134, 1, // Opcode: FSAF_W
/* 9178 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 9191
/* 9182 */    MCD::OPC_CheckPredicate, 7, 71, 17, // Skip to: 13609
/* 9186 */    MCD::OPC_Decode, 134, 6, 135, 1, // Opcode: FSAF_D
/* 9191 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 9204
/* 9195 */    MCD::OPC_CheckPredicate, 7, 58, 17, // Skip to: 13609
/* 9199 */    MCD::OPC_Decode, 169, 6, 134, 1, // Opcode: FSUN_W
/* 9204 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 9217
/* 9208 */    MCD::OPC_CheckPredicate, 7, 45, 17, // Skip to: 13609
/* 9212 */    MCD::OPC_Decode, 168, 6, 135, 1, // Opcode: FSUN_D
/* 9217 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 9230
/* 9221 */    MCD::OPC_CheckPredicate, 7, 32, 17, // Skip to: 13609
/* 9225 */    MCD::OPC_Decode, 137, 6, 134, 1, // Opcode: FSEQ_W
/* 9230 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 9243
/* 9234 */    MCD::OPC_CheckPredicate, 7, 19, 17, // Skip to: 13609
/* 9238 */    MCD::OPC_Decode, 136, 6, 135, 1, // Opcode: FSEQ_D
/* 9243 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 9256
/* 9247 */    MCD::OPC_CheckPredicate, 7, 6, 17, // Skip to: 13609
/* 9251 */    MCD::OPC_Decode, 161, 6, 134, 1, // Opcode: FSUEQ_W
/* 9256 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 9269
/* 9260 */    MCD::OPC_CheckPredicate, 7, 249, 16, // Skip to: 13609
/* 9264 */    MCD::OPC_Decode, 160, 6, 135, 1, // Opcode: FSUEQ_D
/* 9269 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 9282
/* 9273 */    MCD::OPC_CheckPredicate, 7, 236, 16, // Skip to: 13609
/* 9277 */    MCD::OPC_Decode, 141, 6, 134, 1, // Opcode: FSLT_W
/* 9282 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 9295
/* 9286 */    MCD::OPC_CheckPredicate, 7, 223, 16, // Skip to: 13609
/* 9290 */    MCD::OPC_Decode, 140, 6, 135, 1, // Opcode: FSLT_D
/* 9295 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 9308
/* 9299 */    MCD::OPC_CheckPredicate, 7, 210, 16, // Skip to: 13609
/* 9303 */    MCD::OPC_Decode, 165, 6, 134, 1, // Opcode: FSULT_W
/* 9308 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 9321
/* 9312 */    MCD::OPC_CheckPredicate, 7, 197, 16, // Skip to: 13609
/* 9316 */    MCD::OPC_Decode, 164, 6, 135, 1, // Opcode: FSULT_D
/* 9321 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 9334
/* 9325 */    MCD::OPC_CheckPredicate, 7, 184, 16, // Skip to: 13609
/* 9329 */    MCD::OPC_Decode, 139, 6, 134, 1, // Opcode: FSLE_W
/* 9334 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 9347
/* 9338 */    MCD::OPC_CheckPredicate, 7, 171, 16, // Skip to: 13609
/* 9342 */    MCD::OPC_Decode, 138, 6, 135, 1, // Opcode: FSLE_D
/* 9347 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 9360
/* 9351 */    MCD::OPC_CheckPredicate, 7, 158, 16, // Skip to: 13609
/* 9355 */    MCD::OPC_Decode, 163, 6, 134, 1, // Opcode: FSULE_W
/* 9360 */    MCD::OPC_FilterValue, 31, 149, 16, // Skip to: 13609
/* 9364 */    MCD::OPC_CheckPredicate, 7, 145, 16, // Skip to: 13609
/* 9368 */    MCD::OPC_Decode, 162, 6, 135, 1, // Opcode: FSULE_D
/* 9373 */    MCD::OPC_FilterValue, 27, 85, 1, // Skip to: 9718
/* 9377 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 9380 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 9393
/* 9384 */    MCD::OPC_CheckPredicate, 7, 125, 16, // Skip to: 13609
/* 9388 */    MCD::OPC_Decode, 157, 5, 134, 1, // Opcode: FADD_W
/* 9393 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 9406
/* 9397 */    MCD::OPC_CheckPredicate, 7, 112, 16, // Skip to: 13609
/* 9401 */    MCD::OPC_Decode, 151, 5, 135, 1, // Opcode: FADD_D
/* 9406 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 9419
/* 9410 */    MCD::OPC_CheckPredicate, 7, 99, 16, // Skip to: 13609
/* 9414 */    MCD::OPC_Decode, 159, 6, 134, 1, // Opcode: FSUB_W
/* 9419 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 9432
/* 9423 */    MCD::OPC_CheckPredicate, 7, 86, 16, // Skip to: 13609
/* 9427 */    MCD::OPC_Decode, 153, 6, 135, 1, // Opcode: FSUB_D
/* 9432 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 9445
/* 9436 */    MCD::OPC_CheckPredicate, 7, 73, 16, // Skip to: 13609
/* 9440 */    MCD::OPC_Decode, 250, 5, 134, 1, // Opcode: FMUL_W
/* 9445 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 9458
/* 9449 */    MCD::OPC_CheckPredicate, 7, 60, 16, // Skip to: 13609
/* 9453 */    MCD::OPC_Decode, 244, 5, 135, 1, // Opcode: FMUL_D
/* 9458 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 9471
/* 9462 */    MCD::OPC_CheckPredicate, 7, 47, 16, // Skip to: 13609
/* 9466 */    MCD::OPC_Decode, 193, 5, 134, 1, // Opcode: FDIV_W
/* 9471 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 9484
/* 9475 */    MCD::OPC_CheckPredicate, 7, 34, 16, // Skip to: 13609
/* 9479 */    MCD::OPC_Decode, 187, 5, 135, 1, // Opcode: FDIV_D
/* 9484 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 9497
/* 9488 */    MCD::OPC_CheckPredicate, 7, 21, 16, // Skip to: 13609
/* 9492 */    MCD::OPC_Decode, 228, 5, 138, 1, // Opcode: FMADD_W
/* 9497 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 9510
/* 9501 */    MCD::OPC_CheckPredicate, 7, 8, 16, // Skip to: 13609
/* 9505 */    MCD::OPC_Decode, 227, 5, 139, 1, // Opcode: FMADD_D
/* 9510 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 9523
/* 9514 */    MCD::OPC_CheckPredicate, 7, 251, 15, // Skip to: 13609
/* 9518 */    MCD::OPC_Decode, 243, 5, 138, 1, // Opcode: FMSUB_W
/* 9523 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 9536
/* 9527 */    MCD::OPC_CheckPredicate, 7, 238, 15, // Skip to: 13609
/* 9531 */    MCD::OPC_Decode, 242, 5, 139, 1, // Opcode: FMSUB_D
/* 9536 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 9549
/* 9540 */    MCD::OPC_CheckPredicate, 7, 225, 15, // Skip to: 13609
/* 9544 */    MCD::OPC_Decode, 198, 5, 134, 1, // Opcode: FEXP2_W
/* 9549 */    MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 9562
/* 9553 */    MCD::OPC_CheckPredicate, 7, 212, 15, // Skip to: 13609
/* 9557 */    MCD::OPC_Decode, 196, 5, 135, 1, // Opcode: FEXP2_D
/* 9562 */    MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 9575
/* 9566 */    MCD::OPC_CheckPredicate, 7, 199, 15, // Skip to: 13609
/* 9570 */    MCD::OPC_Decode, 194, 5, 174, 1, // Opcode: FEXDO_H
/* 9575 */    MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 9588
/* 9579 */    MCD::OPC_CheckPredicate, 7, 186, 15, // Skip to: 13609
/* 9583 */    MCD::OPC_Decode, 195, 5, 175, 1, // Opcode: FEXDO_W
/* 9588 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 9601
/* 9592 */    MCD::OPC_CheckPredicate, 7, 173, 15, // Skip to: 13609
/* 9596 */    MCD::OPC_Decode, 174, 6, 174, 1, // Opcode: FTQ_H
/* 9601 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 9614
/* 9605 */    MCD::OPC_CheckPredicate, 7, 160, 15, // Skip to: 13609
/* 9609 */    MCD::OPC_Decode, 175, 6, 175, 1, // Opcode: FTQ_W
/* 9614 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 9627
/* 9618 */    MCD::OPC_CheckPredicate, 7, 147, 15, // Skip to: 13609
/* 9622 */    MCD::OPC_Decode, 236, 5, 134, 1, // Opcode: FMIN_W
/* 9627 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 9640
/* 9631 */    MCD::OPC_CheckPredicate, 7, 134, 15, // Skip to: 13609
/* 9635 */    MCD::OPC_Decode, 235, 5, 135, 1, // Opcode: FMIN_D
/* 9640 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 9653
/* 9644 */    MCD::OPC_CheckPredicate, 7, 121, 15, // Skip to: 13609
/* 9648 */    MCD::OPC_Decode, 234, 5, 134, 1, // Opcode: FMIN_A_W
/* 9653 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 9666
/* 9657 */    MCD::OPC_CheckPredicate, 7, 108, 15, // Skip to: 13609
/* 9661 */    MCD::OPC_Decode, 233, 5, 135, 1, // Opcode: FMIN_A_D
/* 9666 */    MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 9679
/* 9670 */    MCD::OPC_CheckPredicate, 7, 95, 15, // Skip to: 13609
/* 9674 */    MCD::OPC_Decode, 232, 5, 134, 1, // Opcode: FMAX_W
/* 9679 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 9692
/* 9683 */    MCD::OPC_CheckPredicate, 7, 82, 15, // Skip to: 13609
/* 9687 */    MCD::OPC_Decode, 231, 5, 135, 1, // Opcode: FMAX_D
/* 9692 */    MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 9705
/* 9696 */    MCD::OPC_CheckPredicate, 7, 69, 15, // Skip to: 13609
/* 9700 */    MCD::OPC_Decode, 230, 5, 134, 1, // Opcode: FMAX_A_W
/* 9705 */    MCD::OPC_FilterValue, 31, 60, 15, // Skip to: 13609
/* 9709 */    MCD::OPC_CheckPredicate, 7, 56, 15, // Skip to: 13609
/* 9713 */    MCD::OPC_Decode, 229, 5, 135, 1, // Opcode: FMAX_A_D
/* 9718 */    MCD::OPC_FilterValue, 28, 59, 1, // Skip to: 10037
/* 9722 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 9725 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 9738
/* 9729 */    MCD::OPC_CheckPredicate, 7, 36, 15, // Skip to: 13609
/* 9733 */    MCD::OPC_Decode, 176, 5, 134, 1, // Opcode: FCOR_W
/* 9738 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 9751
/* 9742 */    MCD::OPC_CheckPredicate, 7, 23, 15, // Skip to: 13609
/* 9746 */    MCD::OPC_Decode, 175, 5, 135, 1, // Opcode: FCOR_D
/* 9751 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 9764
/* 9755 */    MCD::OPC_CheckPredicate, 7, 10, 15, // Skip to: 13609
/* 9759 */    MCD::OPC_Decode, 184, 5, 134, 1, // Opcode: FCUNE_W
/* 9764 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 9777
/* 9768 */    MCD::OPC_CheckPredicate, 7, 253, 14, // Skip to: 13609
/* 9772 */    MCD::OPC_Decode, 183, 5, 135, 1, // Opcode: FCUNE_D
/* 9777 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 9790
/* 9781 */    MCD::OPC_CheckPredicate, 7, 240, 14, // Skip to: 13609
/* 9785 */    MCD::OPC_Decode, 174, 5, 134, 1, // Opcode: FCNE_W
/* 9790 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 9803
/* 9794 */    MCD::OPC_CheckPredicate, 7, 227, 14, // Skip to: 13609
/* 9798 */    MCD::OPC_Decode, 173, 5, 135, 1, // Opcode: FCNE_D
/* 9803 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 9816
/* 9807 */    MCD::OPC_CheckPredicate, 7, 214, 14, // Skip to: 13609
/* 9811 */    MCD::OPC_Decode, 194, 9, 133, 1, // Opcode: MUL_Q_H
/* 9816 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 9829
/* 9820 */    MCD::OPC_CheckPredicate, 7, 201, 14, // Skip to: 13609
/* 9824 */    MCD::OPC_Decode, 195, 9, 134, 1, // Opcode: MUL_Q_W
/* 9829 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 9842
/* 9833 */    MCD::OPC_CheckPredicate, 7, 188, 14, // Skip to: 13609
/* 9837 */    MCD::OPC_Decode, 251, 7, 137, 1, // Opcode: MADD_Q_H
/* 9842 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 9855
/* 9846 */    MCD::OPC_CheckPredicate, 7, 175, 14, // Skip to: 13609
/* 9850 */    MCD::OPC_Decode, 252, 7, 138, 1, // Opcode: MADD_Q_W
/* 9855 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 9868
/* 9859 */    MCD::OPC_CheckPredicate, 7, 162, 14, // Skip to: 13609
/* 9863 */    MCD::OPC_Decode, 140, 9, 137, 1, // Opcode: MSUB_Q_H
/* 9868 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 9881
/* 9872 */    MCD::OPC_CheckPredicate, 7, 149, 14, // Skip to: 13609
/* 9876 */    MCD::OPC_Decode, 141, 9, 138, 1, // Opcode: MSUB_Q_W
/* 9881 */    MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 9894
/* 9885 */    MCD::OPC_CheckPredicate, 7, 136, 14, // Skip to: 13609
/* 9889 */    MCD::OPC_Decode, 145, 6, 134, 1, // Opcode: FSOR_W
/* 9894 */    MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 9907
/* 9898 */    MCD::OPC_CheckPredicate, 7, 123, 14, // Skip to: 13609
/* 9902 */    MCD::OPC_Decode, 144, 6, 135, 1, // Opcode: FSOR_D
/* 9907 */    MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 9920
/* 9911 */    MCD::OPC_CheckPredicate, 7, 110, 14, // Skip to: 13609
/* 9915 */    MCD::OPC_Decode, 167, 6, 134, 1, // Opcode: FSUNE_W
/* 9920 */    MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 9933
/* 9924 */    MCD::OPC_CheckPredicate, 7, 97, 14, // Skip to: 13609
/* 9928 */    MCD::OPC_Decode, 166, 6, 135, 1, // Opcode: FSUNE_D
/* 9933 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 9946
/* 9937 */    MCD::OPC_CheckPredicate, 7, 84, 14, // Skip to: 13609
/* 9941 */    MCD::OPC_Decode, 143, 6, 134, 1, // Opcode: FSNE_W
/* 9946 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 9959
/* 9950 */    MCD::OPC_CheckPredicate, 7, 71, 14, // Skip to: 13609
/* 9954 */    MCD::OPC_Decode, 142, 6, 135, 1, // Opcode: FSNE_D
/* 9959 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 9972
/* 9963 */    MCD::OPC_CheckPredicate, 7, 58, 14, // Skip to: 13609
/* 9967 */    MCD::OPC_Decode, 177, 9, 133, 1, // Opcode: MULR_Q_H
/* 9972 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 9985
/* 9976 */    MCD::OPC_CheckPredicate, 7, 45, 14, // Skip to: 13609
/* 9980 */    MCD::OPC_Decode, 178, 9, 134, 1, // Opcode: MULR_Q_W
/* 9985 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 9998
/* 9989 */    MCD::OPC_CheckPredicate, 7, 32, 14, // Skip to: 13609
/* 9993 */    MCD::OPC_Decode, 237, 7, 137, 1, // Opcode: MADDR_Q_H
/* 9998 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 10011
/* 10002 */   MCD::OPC_CheckPredicate, 7, 19, 14, // Skip to: 13609
/* 10006 */   MCD::OPC_Decode, 238, 7, 138, 1, // Opcode: MADDR_Q_W
/* 10011 */   MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 10024
/* 10015 */   MCD::OPC_CheckPredicate, 7, 6, 14, // Skip to: 13609
/* 10019 */   MCD::OPC_Decode, 254, 8, 137, 1, // Opcode: MSUBR_Q_H
/* 10024 */   MCD::OPC_FilterValue, 29, 253, 13, // Skip to: 13609
/* 10028 */   MCD::OPC_CheckPredicate, 7, 249, 13, // Skip to: 13609
/* 10032 */   MCD::OPC_Decode, 255, 8, 138, 1, // Opcode: MSUBR_Q_W
/* 10037 */   MCD::OPC_FilterValue, 30, 219, 2, // Skip to: 10772
/* 10041 */   MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 10044 */   MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 10056
/* 10048 */   MCD::OPC_CheckPredicate, 7, 229, 13, // Skip to: 13609
/* 10052 */   MCD::OPC_Decode, 88, 132, 1, // Opcode: AND_V
/* 10056 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 10069
/* 10060 */   MCD::OPC_CheckPredicate, 7, 217, 13, // Skip to: 13609
/* 10064 */   MCD::OPC_Decode, 241, 9, 132, 1, // Opcode: OR_V
/* 10069 */   MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 10082
/* 10073 */   MCD::OPC_CheckPredicate, 7, 204, 13, // Skip to: 13609
/* 10077 */   MCD::OPC_Decode, 229, 9, 132, 1, // Opcode: NOR_V
/* 10082 */   MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 10095
/* 10086 */   MCD::OPC_CheckPredicate, 7, 191, 13, // Skip to: 13609
/* 10090 */   MCD::OPC_Decode, 215, 13, 132, 1, // Opcode: XOR_V
/* 10095 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 10108
/* 10099 */   MCD::OPC_CheckPredicate, 7, 178, 13, // Skip to: 13609
/* 10103 */   MCD::OPC_Decode, 252, 1, 136, 1, // Opcode: BMNZ_V
/* 10108 */   MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 10121
/* 10112 */   MCD::OPC_CheckPredicate, 7, 165, 13, // Skip to: 13609
/* 10116 */   MCD::OPC_Decode, 254, 1, 136, 1, // Opcode: BMZ_V
/* 10121 */   MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 10134
/* 10125 */   MCD::OPC_CheckPredicate, 7, 152, 13, // Skip to: 13609
/* 10129 */   MCD::OPC_Decode, 161, 2, 136, 1, // Opcode: BSEL_V
/* 10134 */   MCD::OPC_FilterValue, 24, 211, 0, // Skip to: 10349
/* 10138 */   MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 10141 */   MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 10154
/* 10145 */   MCD::OPC_CheckPredicate, 7, 132, 13, // Skip to: 13609
/* 10149 */   MCD::OPC_Decode, 212, 5, 176, 1, // Opcode: FILL_B
/* 10154 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 10167
/* 10158 */   MCD::OPC_CheckPredicate, 7, 119, 13, // Skip to: 13609
/* 10162 */   MCD::OPC_Decode, 216, 5, 177, 1, // Opcode: FILL_H
/* 10167 */   MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 10180
/* 10171 */   MCD::OPC_CheckPredicate, 7, 106, 13, // Skip to: 13609
/* 10175 */   MCD::OPC_Decode, 217, 5, 178, 1, // Opcode: FILL_W
/* 10180 */   MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 10193
/* 10184 */   MCD::OPC_CheckPredicate, 13, 93, 13, // Skip to: 13609
/* 10188 */   MCD::OPC_Decode, 213, 5, 179, 1, // Opcode: FILL_D
/* 10193 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 10206
/* 10197 */   MCD::OPC_CheckPredicate, 7, 80, 13, // Skip to: 13609
/* 10201 */   MCD::OPC_Decode, 132, 10, 168, 1, // Opcode: PCNT_B
/* 10206 */   MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 10219
/* 10210 */   MCD::OPC_CheckPredicate, 7, 67, 13, // Skip to: 13609
/* 10214 */   MCD::OPC_Decode, 134, 10, 180, 1, // Opcode: PCNT_H
/* 10219 */   MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 10232
/* 10223 */   MCD::OPC_CheckPredicate, 7, 54, 13, // Skip to: 13609
/* 10227 */   MCD::OPC_Decode, 135, 10, 181, 1, // Opcode: PCNT_W
/* 10232 */   MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 10245
/* 10236 */   MCD::OPC_CheckPredicate, 7, 41, 13, // Skip to: 13609
/* 10240 */   MCD::OPC_Decode, 133, 10, 182, 1, // Opcode: PCNT_D
/* 10245 */   MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 10258
/* 10249 */   MCD::OPC_CheckPredicate, 7, 28, 13, // Skip to: 13609
/* 10253 */   MCD::OPC_Decode, 206, 9, 168, 1, // Opcode: NLOC_B
/* 10258 */   MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 10271
/* 10262 */   MCD::OPC_CheckPredicate, 7, 15, 13, // Skip to: 13609
/* 10266 */   MCD::OPC_Decode, 208, 9, 180, 1, // Opcode: NLOC_H
/* 10271 */   MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 10284
/* 10275 */   MCD::OPC_CheckPredicate, 7, 2, 13, // Skip to: 13609
/* 10279 */   MCD::OPC_Decode, 209, 9, 181, 1, // Opcode: NLOC_W
/* 10284 */   MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 10297
/* 10288 */   MCD::OPC_CheckPredicate, 7, 245, 12, // Skip to: 13609
/* 10292 */   MCD::OPC_Decode, 207, 9, 182, 1, // Opcode: NLOC_D
/* 10297 */   MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 10310
/* 10301 */   MCD::OPC_CheckPredicate, 7, 232, 12, // Skip to: 13609
/* 10305 */   MCD::OPC_Decode, 210, 9, 168, 1, // Opcode: NLZC_B
/* 10310 */   MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 10323
/* 10314 */   MCD::OPC_CheckPredicate, 7, 219, 12, // Skip to: 13609
/* 10318 */   MCD::OPC_Decode, 212, 9, 180, 1, // Opcode: NLZC_H
/* 10323 */   MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 10336
/* 10327 */   MCD::OPC_CheckPredicate, 7, 206, 12, // Skip to: 13609
/* 10331 */   MCD::OPC_Decode, 213, 9, 181, 1, // Opcode: NLZC_W
/* 10336 */   MCD::OPC_FilterValue, 15, 197, 12, // Skip to: 13609
/* 10340 */   MCD::OPC_CheckPredicate, 7, 193, 12, // Skip to: 13609
/* 10344 */   MCD::OPC_Decode, 211, 9, 182, 1, // Opcode: NLZC_D
/* 10349 */   MCD::OPC_FilterValue, 25, 184, 12, // Skip to: 13609
/* 10353 */   MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 10356 */   MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 10369
/* 10360 */   MCD::OPC_CheckPredicate, 7, 173, 12, // Skip to: 13609
/* 10364 */   MCD::OPC_Decode, 163, 5, 181, 1, // Opcode: FCLASS_W
/* 10369 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 10382
/* 10373 */   MCD::OPC_CheckPredicate, 7, 160, 12, // Skip to: 13609
/* 10377 */   MCD::OPC_Decode, 162, 5, 182, 1, // Opcode: FCLASS_D
/* 10382 */   MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 10395
/* 10386 */   MCD::OPC_CheckPredicate, 7, 147, 12, // Skip to: 13609
/* 10390 */   MCD::OPC_Decode, 177, 6, 181, 1, // Opcode: FTRUNC_S_W
/* 10395 */   MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 10408
/* 10399 */   MCD::OPC_CheckPredicate, 7, 134, 12, // Skip to: 13609
/* 10403 */   MCD::OPC_Decode, 176, 6, 182, 1, // Opcode: FTRUNC_S_D
/* 10408 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 10421
/* 10412 */   MCD::OPC_CheckPredicate, 7, 121, 12, // Skip to: 13609
/* 10416 */   MCD::OPC_Decode, 179, 6, 181, 1, // Opcode: FTRUNC_U_W
/* 10421 */   MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 10434
/* 10425 */   MCD::OPC_CheckPredicate, 7, 108, 12, // Skip to: 13609
/* 10429 */   MCD::OPC_Decode, 178, 6, 182, 1, // Opcode: FTRUNC_U_D
/* 10434 */   MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 10447
/* 10438 */   MCD::OPC_CheckPredicate, 7, 95, 12, // Skip to: 13609
/* 10442 */   MCD::OPC_Decode, 152, 6, 181, 1, // Opcode: FSQRT_W
/* 10447 */   MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 10460
/* 10451 */   MCD::OPC_CheckPredicate, 7, 82, 12, // Skip to: 13609
/* 10455 */   MCD::OPC_Decode, 146, 6, 182, 1, // Opcode: FSQRT_D
/* 10460 */   MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 10473
/* 10464 */   MCD::OPC_CheckPredicate, 7, 69, 12, // Skip to: 13609
/* 10468 */   MCD::OPC_Decode, 133, 6, 181, 1, // Opcode: FRSQRT_W
/* 10473 */   MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 10486
/* 10477 */   MCD::OPC_CheckPredicate, 7, 56, 12, // Skip to: 13609
/* 10481 */   MCD::OPC_Decode, 132, 6, 182, 1, // Opcode: FRSQRT_D
/* 10486 */   MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 10499
/* 10490 */   MCD::OPC_CheckPredicate, 7, 43, 12, // Skip to: 13609
/* 10494 */   MCD::OPC_Decode, 129, 6, 181, 1, // Opcode: FRCP_W
/* 10499 */   MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 10512
/* 10503 */   MCD::OPC_CheckPredicate, 7, 30, 12, // Skip to: 13609
/* 10507 */   MCD::OPC_Decode, 128, 6, 182, 1, // Opcode: FRCP_D
/* 10512 */   MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 10525
/* 10516 */   MCD::OPC_CheckPredicate, 7, 17, 12, // Skip to: 13609
/* 10520 */   MCD::OPC_Decode, 131, 6, 181, 1, // Opcode: FRINT_W
/* 10525 */   MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 10538
/* 10529 */   MCD::OPC_CheckPredicate, 7, 4, 12, // Skip to: 13609
/* 10533 */   MCD::OPC_Decode, 130, 6, 182, 1, // Opcode: FRINT_D
/* 10538 */   MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 10551
/* 10542 */   MCD::OPC_CheckPredicate, 7, 247, 11, // Skip to: 13609
/* 10546 */   MCD::OPC_Decode, 219, 5, 181, 1, // Opcode: FLOG2_W
/* 10551 */   MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 10564
/* 10555 */   MCD::OPC_CheckPredicate, 7, 234, 11, // Skip to: 13609
/* 10559 */   MCD::OPC_Decode, 218, 5, 182, 1, // Opcode: FLOG2_D
/* 10564 */   MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 10577
/* 10568 */   MCD::OPC_CheckPredicate, 7, 221, 11, // Skip to: 13609
/* 10572 */   MCD::OPC_Decode, 201, 5, 183, 1, // Opcode: FEXUPL_W
/* 10577 */   MCD::OPC_FilterValue, 17, 9, 0, // Skip to: 10590
/* 10581 */   MCD::OPC_CheckPredicate, 7, 208, 11, // Skip to: 13609
/* 10585 */   MCD::OPC_Decode, 200, 5, 184, 1, // Opcode: FEXUPL_D
/* 10590 */   MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 10603
/* 10594 */   MCD::OPC_CheckPredicate, 7, 195, 11, // Skip to: 13609
/* 10598 */   MCD::OPC_Decode, 203, 5, 183, 1, // Opcode: FEXUPR_W
/* 10603 */   MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 10616
/* 10607 */   MCD::OPC_CheckPredicate, 7, 182, 11, // Skip to: 13609
/* 10611 */   MCD::OPC_Decode, 202, 5, 184, 1, // Opcode: FEXUPR_D
/* 10616 */   MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 10629
/* 10620 */   MCD::OPC_CheckPredicate, 7, 169, 11, // Skip to: 13609
/* 10624 */   MCD::OPC_Decode, 209, 5, 183, 1, // Opcode: FFQL_W
/* 10629 */   MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 10642
/* 10633 */   MCD::OPC_CheckPredicate, 7, 156, 11, // Skip to: 13609
/* 10637 */   MCD::OPC_Decode, 208, 5, 184, 1, // Opcode: FFQL_D
/* 10642 */   MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 10655
/* 10646 */   MCD::OPC_CheckPredicate, 7, 143, 11, // Skip to: 13609
/* 10650 */   MCD::OPC_Decode, 211, 5, 183, 1, // Opcode: FFQR_W
/* 10655 */   MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 10668
/* 10659 */   MCD::OPC_CheckPredicate, 7, 130, 11, // Skip to: 13609
/* 10663 */   MCD::OPC_Decode, 210, 5, 184, 1, // Opcode: FFQR_D
/* 10668 */   MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 10681
/* 10672 */   MCD::OPC_CheckPredicate, 7, 117, 11, // Skip to: 13609
/* 10676 */   MCD::OPC_Decode, 171, 6, 181, 1, // Opcode: FTINT_S_W
/* 10681 */   MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 10694
/* 10685 */   MCD::OPC_CheckPredicate, 7, 104, 11, // Skip to: 13609
/* 10689 */   MCD::OPC_Decode, 170, 6, 182, 1, // Opcode: FTINT_S_D
/* 10694 */   MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 10707
/* 10698 */   MCD::OPC_CheckPredicate, 7, 91, 11, // Skip to: 13609
/* 10702 */   MCD::OPC_Decode, 173, 6, 181, 1, // Opcode: FTINT_U_W
/* 10707 */   MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 10720
/* 10711 */   MCD::OPC_CheckPredicate, 7, 78, 11, // Skip to: 13609
/* 10715 */   MCD::OPC_Decode, 172, 6, 182, 1, // Opcode: FTINT_U_D
/* 10720 */   MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 10733
/* 10724 */   MCD::OPC_CheckPredicate, 7, 65, 11, // Skip to: 13609
/* 10728 */   MCD::OPC_Decode, 205, 5, 181, 1, // Opcode: FFINT_S_W
/* 10733 */   MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 10746
/* 10737 */   MCD::OPC_CheckPredicate, 7, 52, 11, // Skip to: 13609
/* 10741 */   MCD::OPC_Decode, 204, 5, 182, 1, // Opcode: FFINT_S_D
/* 10746 */   MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 10759
/* 10750 */   MCD::OPC_CheckPredicate, 7, 39, 11, // Skip to: 13609
/* 10754 */   MCD::OPC_Decode, 207, 5, 181, 1, // Opcode: FFINT_U_W
/* 10759 */   MCD::OPC_FilterValue, 31, 30, 11, // Skip to: 13609
/* 10763 */   MCD::OPC_CheckPredicate, 7, 26, 11, // Skip to: 13609
/* 10767 */   MCD::OPC_Decode, 206, 5, 182, 1, // Opcode: FFINT_U_D
/* 10772 */   MCD::OPC_FilterValue, 32, 9, 0, // Skip to: 10785
/* 10776 */   MCD::OPC_CheckPredicate, 7, 13, 11, // Skip to: 13609
/* 10780 */   MCD::OPC_Decode, 155, 7, 185, 1, // Opcode: LD_B
/* 10785 */   MCD::OPC_FilterValue, 33, 9, 0, // Skip to: 10798
/* 10789 */   MCD::OPC_CheckPredicate, 7, 0, 11, // Skip to: 13609
/* 10793 */   MCD::OPC_Decode, 157, 7, 185, 1, // Opcode: LD_H
/* 10798 */   MCD::OPC_FilterValue, 34, 9, 0, // Skip to: 10811
/* 10802 */   MCD::OPC_CheckPredicate, 7, 243, 10, // Skip to: 13609
/* 10806 */   MCD::OPC_Decode, 158, 7, 185, 1, // Opcode: LD_W
/* 10811 */   MCD::OPC_FilterValue, 35, 9, 0, // Skip to: 10824
/* 10815 */   MCD::OPC_CheckPredicate, 7, 230, 10, // Skip to: 13609
/* 10819 */   MCD::OPC_Decode, 156, 7, 185, 1, // Opcode: LD_D
/* 10824 */   MCD::OPC_FilterValue, 36, 9, 0, // Skip to: 10837
/* 10828 */   MCD::OPC_CheckPredicate, 7, 217, 10, // Skip to: 13609
/* 10832 */   MCD::OPC_Decode, 161, 12, 185, 1, // Opcode: ST_B
/* 10837 */   MCD::OPC_FilterValue, 37, 9, 0, // Skip to: 10850
/* 10841 */   MCD::OPC_CheckPredicate, 7, 204, 10, // Skip to: 13609
/* 10845 */   MCD::OPC_Decode, 163, 12, 185, 1, // Opcode: ST_H
/* 10850 */   MCD::OPC_FilterValue, 38, 9, 0, // Skip to: 10863
/* 10854 */   MCD::OPC_CheckPredicate, 7, 191, 10, // Skip to: 13609
/* 10858 */   MCD::OPC_Decode, 164, 12, 185, 1, // Opcode: ST_W
/* 10863 */   MCD::OPC_FilterValue, 39, 182, 10, // Skip to: 13609
/* 10867 */   MCD::OPC_CheckPredicate, 7, 178, 10, // Skip to: 13609
/* 10871 */   MCD::OPC_Decode, 162, 12, 185, 1, // Opcode: ST_D
/* 10876 */   MCD::OPC_FilterValue, 31, 113, 9, // Skip to: 13297
/* 10880 */   MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 10883 */   MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 10896
/* 10887 */   MCD::OPC_CheckPredicate, 4, 158, 10, // Skip to: 13609
/* 10891 */   MCD::OPC_Decode, 254, 4, 186, 1, // Opcode: EXT
/* 10896 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 10909
/* 10900 */   MCD::OPC_CheckPredicate, 4, 145, 10, // Skip to: 13609
/* 10904 */   MCD::OPC_Decode, 209, 6, 187, 1, // Opcode: INS
/* 10909 */   MCD::OPC_FilterValue, 10, 42, 0, // Skip to: 10955
/* 10913 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 10916 */   MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 10929
/* 10920 */   MCD::OPC_CheckPredicate, 11, 125, 10, // Skip to: 13609
/* 10924 */   MCD::OPC_Decode, 212, 7, 188, 1, // Opcode: LWX
/* 10929 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 10942
/* 10933 */   MCD::OPC_CheckPredicate, 11, 112, 10, // Skip to: 13609
/* 10937 */   MCD::OPC_Decode, 165, 7, 188, 1, // Opcode: LHX
/* 10942 */   MCD::OPC_FilterValue, 6, 103, 10, // Skip to: 13609
/* 10946 */   MCD::OPC_CheckPredicate, 11, 99, 10, // Skip to: 13609
/* 10950 */   MCD::OPC_Decode, 134, 7, 188, 1, // Opcode: LBUX
/* 10955 */   MCD::OPC_FilterValue, 12, 15, 0, // Skip to: 10974
/* 10959 */   MCD::OPC_CheckPredicate, 11, 86, 10, // Skip to: 13609
/* 10963 */   MCD::OPC_CheckField, 6, 10, 0, 80, 10, // Skip to: 13609
/* 10969 */   MCD::OPC_Decode, 222, 6, 189, 1, // Opcode: INSV
/* 10974 */   MCD::OPC_FilterValue, 16, 51, 1, // Skip to: 11285
/* 10978 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 10981 */   MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 10993
/* 10985 */   MCD::OPC_CheckPredicate, 11, 60, 10, // Skip to: 13609
/* 10989 */   MCD::OPC_Decode, 55, 190, 1, // Opcode: ADDU_QB
/* 10993 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 11006
/* 10997 */   MCD::OPC_CheckPredicate, 11, 48, 10, // Skip to: 13609
/* 11001 */   MCD::OPC_Decode, 193, 12, 190, 1, // Opcode: SUBU_QB
/* 11006 */   MCD::OPC_FilterValue, 4, 8, 0, // Skip to: 11018
/* 11010 */   MCD::OPC_CheckPredicate, 11, 35, 10, // Skip to: 13609
/* 11014 */   MCD::OPC_Decode, 57, 190, 1, // Opcode: ADDU_S_QB
/* 11018 */   MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 11031
/* 11022 */   MCD::OPC_CheckPredicate, 11, 23, 10, // Skip to: 13609
/* 11026 */   MCD::OPC_Decode, 195, 12, 190, 1, // Opcode: SUBU_S_QB
/* 11031 */   MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 11044
/* 11035 */   MCD::OPC_CheckPredicate, 11, 10, 10, // Skip to: 13609
/* 11039 */   MCD::OPC_Decode, 171, 9, 190, 1, // Opcode: MULEU_S_PH_QBL
/* 11044 */   MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 11057
/* 11048 */   MCD::OPC_CheckPredicate, 11, 253, 9, // Skip to: 13609
/* 11052 */   MCD::OPC_Decode, 172, 9, 190, 1, // Opcode: MULEU_S_PH_QBR
/* 11057 */   MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 11069
/* 11061 */   MCD::OPC_CheckPredicate, 29, 240, 9, // Skip to: 13609
/* 11065 */   MCD::OPC_Decode, 54, 190, 1, // Opcode: ADDU_PH
/* 11069 */   MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 11082
/* 11073 */   MCD::OPC_CheckPredicate, 29, 228, 9, // Skip to: 13609
/* 11077 */   MCD::OPC_Decode, 192, 12, 190, 1, // Opcode: SUBU_PH
/* 11082 */   MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 11094
/* 11086 */   MCD::OPC_CheckPredicate, 11, 215, 9, // Skip to: 13609
/* 11090 */   MCD::OPC_Decode, 35, 190, 1, // Opcode: ADDQ_PH
/* 11094 */   MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 11107
/* 11098 */   MCD::OPC_CheckPredicate, 11, 203, 9, // Skip to: 13609
/* 11102 */   MCD::OPC_Decode, 170, 12, 190, 1, // Opcode: SUBQ_PH
/* 11107 */   MCD::OPC_FilterValue, 12, 8, 0, // Skip to: 11119
/* 11111 */   MCD::OPC_CheckPredicate, 29, 190, 9, // Skip to: 13609
/* 11115 */   MCD::OPC_Decode, 56, 190, 1, // Opcode: ADDU_S_PH
/* 11119 */   MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 11132
/* 11123 */   MCD::OPC_CheckPredicate, 29, 178, 9, // Skip to: 13609
/* 11127 */   MCD::OPC_Decode, 194, 12, 190, 1, // Opcode: SUBU_S_PH
/* 11132 */   MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 11144
/* 11136 */   MCD::OPC_CheckPredicate, 11, 165, 9, // Skip to: 13609
/* 11140 */   MCD::OPC_Decode, 36, 190, 1, // Opcode: ADDQ_S_PH
/* 11144 */   MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 11157
/* 11148 */   MCD::OPC_CheckPredicate, 11, 153, 9, // Skip to: 13609
/* 11152 */   MCD::OPC_Decode, 171, 12, 190, 1, // Opcode: SUBQ_S_PH
/* 11157 */   MCD::OPC_FilterValue, 16, 7, 0, // Skip to: 11168
/* 11161 */   MCD::OPC_CheckPredicate, 11, 140, 9, // Skip to: 13609
/* 11165 */   MCD::OPC_Decode, 38, 32, // Opcode: ADDSC
/* 11168 */   MCD::OPC_FilterValue, 17, 7, 0, // Skip to: 11179
/* 11172 */   MCD::OPC_CheckPredicate, 11, 129, 9, // Skip to: 13609
/* 11176 */   MCD::OPC_Decode, 66, 32, // Opcode: ADDWC
/* 11179 */   MCD::OPC_FilterValue, 18, 8, 0, // Skip to: 11191
/* 11183 */   MCD::OPC_CheckPredicate, 11, 118, 9, // Skip to: 13609
/* 11187 */   MCD::OPC_Decode, 199, 8, 32, // Opcode: MODSUB
/* 11191 */   MCD::OPC_FilterValue, 20, 15, 0, // Skip to: 11210
/* 11195 */   MCD::OPC_CheckPredicate, 11, 106, 9, // Skip to: 13609
/* 11199 */   MCD::OPC_CheckField, 16, 5, 0, 100, 9, // Skip to: 13609
/* 11205 */   MCD::OPC_Decode, 211, 10, 191, 1, // Opcode: RADDU_W_QB
/* 11210 */   MCD::OPC_FilterValue, 22, 7, 0, // Skip to: 11221
/* 11214 */   MCD::OPC_CheckPredicate, 11, 87, 9, // Skip to: 13609
/* 11218 */   MCD::OPC_Decode, 37, 32, // Opcode: ADDQ_S_W
/* 11221 */   MCD::OPC_FilterValue, 23, 8, 0, // Skip to: 11233
/* 11225 */   MCD::OPC_CheckPredicate, 11, 76, 9, // Skip to: 13609
/* 11229 */   MCD::OPC_Decode, 172, 12, 32, // Opcode: SUBQ_S_W
/* 11233 */   MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 11246
/* 11237 */   MCD::OPC_CheckPredicate, 11, 64, 9, // Skip to: 13609
/* 11241 */   MCD::OPC_Decode, 169, 9, 192, 1, // Opcode: MULEQ_S_W_PHL
/* 11246 */   MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 11259
/* 11250 */   MCD::OPC_CheckPredicate, 11, 51, 9, // Skip to: 13609
/* 11254 */   MCD::OPC_Decode, 170, 9, 192, 1, // Opcode: MULEQ_S_W_PHR
/* 11259 */   MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 11272
/* 11263 */   MCD::OPC_CheckPredicate, 29, 38, 9, // Skip to: 13609
/* 11267 */   MCD::OPC_Decode, 175, 9, 190, 1, // Opcode: MULQ_S_PH
/* 11272 */   MCD::OPC_FilterValue, 31, 29, 9, // Skip to: 13609
/* 11276 */   MCD::OPC_CheckPredicate, 11, 25, 9, // Skip to: 13609
/* 11280 */   MCD::OPC_Decode, 173, 9, 190, 1, // Opcode: MULQ_RS_PH
/* 11285 */   MCD::OPC_FilterValue, 17, 69, 1, // Skip to: 11614
/* 11289 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 11292 */   MCD::OPC_FilterValue, 0, 15, 0, // Skip to: 11311
/* 11296 */   MCD::OPC_CheckPredicate, 11, 5, 9, // Skip to: 13609
/* 11300 */   MCD::OPC_CheckField, 11, 5, 0, 255, 8, // Skip to: 13609
/* 11306 */   MCD::OPC_Decode, 142, 3, 193, 1, // Opcode: CMPU_EQ_QB
/* 11311 */   MCD::OPC_FilterValue, 1, 15, 0, // Skip to: 11330
/* 11315 */   MCD::OPC_CheckPredicate, 11, 242, 8, // Skip to: 13609
/* 11319 */   MCD::OPC_CheckField, 11, 5, 0, 236, 8, // Skip to: 13609
/* 11325 */   MCD::OPC_Decode, 144, 3, 193, 1, // Opcode: CMPU_LT_QB
/* 11330 */   MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 11349
/* 11334 */   MCD::OPC_CheckPredicate, 11, 223, 8, // Skip to: 13609
/* 11338 */   MCD::OPC_CheckField, 11, 5, 0, 217, 8, // Skip to: 13609
/* 11344 */   MCD::OPC_Decode, 143, 3, 193, 1, // Opcode: CMPU_LE_QB
/* 11349 */   MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 11362
/* 11353 */   MCD::OPC_CheckPredicate, 11, 204, 8, // Skip to: 13609
/* 11357 */   MCD::OPC_Decode, 137, 10, 190, 1, // Opcode: PICK_QB
/* 11362 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 11375
/* 11366 */   MCD::OPC_CheckPredicate, 11, 191, 8, // Skip to: 13609
/* 11370 */   MCD::OPC_Decode, 139, 3, 192, 1, // Opcode: CMPGU_EQ_QB
/* 11375 */   MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 11388
/* 11379 */   MCD::OPC_CheckPredicate, 11, 178, 8, // Skip to: 13609
/* 11383 */   MCD::OPC_Decode, 141, 3, 192, 1, // Opcode: CMPGU_LT_QB
/* 11388 */   MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 11401
/* 11392 */   MCD::OPC_CheckPredicate, 11, 165, 8, // Skip to: 13609
/* 11396 */   MCD::OPC_Decode, 140, 3, 192, 1, // Opcode: CMPGU_LE_QB
/* 11401 */   MCD::OPC_FilterValue, 8, 15, 0, // Skip to: 11420
/* 11405 */   MCD::OPC_CheckPredicate, 11, 152, 8, // Skip to: 13609
/* 11409 */   MCD::OPC_CheckField, 11, 5, 0, 146, 8, // Skip to: 13609
/* 11415 */   MCD::OPC_Decode, 146, 3, 193, 1, // Opcode: CMP_EQ_PH
/* 11420 */   MCD::OPC_FilterValue, 9, 15, 0, // Skip to: 11439
/* 11424 */   MCD::OPC_CheckPredicate, 11, 133, 8, // Skip to: 13609
/* 11428 */   MCD::OPC_CheckField, 11, 5, 0, 127, 8, // Skip to: 13609
/* 11434 */   MCD::OPC_Decode, 154, 3, 193, 1, // Opcode: CMP_LT_PH
/* 11439 */   MCD::OPC_FilterValue, 10, 15, 0, // Skip to: 11458
/* 11443 */   MCD::OPC_CheckPredicate, 11, 114, 8, // Skip to: 13609
/* 11447 */   MCD::OPC_CheckField, 11, 5, 0, 108, 8, // Skip to: 13609
/* 11453 */   MCD::OPC_Decode, 151, 3, 193, 1, // Opcode: CMP_LE_PH
/* 11458 */   MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 11471
/* 11462 */   MCD::OPC_CheckPredicate, 11, 95, 8, // Skip to: 13609
/* 11466 */   MCD::OPC_Decode, 136, 10, 190, 1, // Opcode: PICK_PH
/* 11471 */   MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 11484
/* 11475 */   MCD::OPC_CheckPredicate, 11, 82, 8, // Skip to: 13609
/* 11479 */   MCD::OPC_Decode, 151, 10, 190, 1, // Opcode: PRECRQ_QB_PH
/* 11484 */   MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 11497
/* 11488 */   MCD::OPC_CheckPredicate, 29, 69, 8, // Skip to: 13609
/* 11492 */   MCD::OPC_Decode, 153, 10, 190, 1, // Opcode: PRECR_QB_PH
/* 11497 */   MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 11510
/* 11501 */   MCD::OPC_CheckPredicate, 11, 56, 8, // Skip to: 13609
/* 11505 */   MCD::OPC_Decode, 249, 9, 190, 1, // Opcode: PACKRL_PH
/* 11510 */   MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 11523
/* 11514 */   MCD::OPC_CheckPredicate, 11, 43, 8, // Skip to: 13609
/* 11518 */   MCD::OPC_Decode, 149, 10, 190, 1, // Opcode: PRECRQU_S_QB_PH
/* 11523 */   MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 11536
/* 11527 */   MCD::OPC_CheckPredicate, 11, 30, 8, // Skip to: 13609
/* 11531 */   MCD::OPC_Decode, 150, 10, 194, 1, // Opcode: PRECRQ_PH_W
/* 11536 */   MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 11549
/* 11540 */   MCD::OPC_CheckPredicate, 11, 17, 8, // Skip to: 13609
/* 11544 */   MCD::OPC_Decode, 152, 10, 194, 1, // Opcode: PRECRQ_RS_PH_W
/* 11549 */   MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 11562
/* 11553 */   MCD::OPC_CheckPredicate, 29, 4, 8, // Skip to: 13609
/* 11557 */   MCD::OPC_Decode, 136, 3, 192, 1, // Opcode: CMPGDU_EQ_QB
/* 11562 */   MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 11575
/* 11566 */   MCD::OPC_CheckPredicate, 29, 247, 7, // Skip to: 13609
/* 11570 */   MCD::OPC_Decode, 138, 3, 192, 1, // Opcode: CMPGDU_LT_QB
/* 11575 */   MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 11588
/* 11579 */   MCD::OPC_CheckPredicate, 29, 234, 7, // Skip to: 13609
/* 11583 */   MCD::OPC_Decode, 137, 3, 192, 1, // Opcode: CMPGDU_LE_QB
/* 11588 */   MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 11601
/* 11592 */   MCD::OPC_CheckPredicate, 29, 221, 7, // Skip to: 13609
/* 11596 */   MCD::OPC_Decode, 154, 10, 195, 1, // Opcode: PRECR_SRA_PH_W
/* 11601 */   MCD::OPC_FilterValue, 31, 212, 7, // Skip to: 13609
/* 11605 */   MCD::OPC_CheckPredicate, 29, 208, 7, // Skip to: 13609
/* 11609 */   MCD::OPC_Decode, 155, 10, 195, 1, // Opcode: PRECR_SRA_R_PH_W
/* 11614 */   MCD::OPC_FilterValue, 18, 74, 1, // Skip to: 11948
/* 11618 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 11621 */   MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 11639
/* 11625 */   MCD::OPC_CheckPredicate, 29, 188, 7, // Skip to: 13609
/* 11629 */   MCD::OPC_CheckField, 21, 5, 0, 182, 7, // Skip to: 13609
/* 11635 */   MCD::OPC_Decode, 23, 196, 1, // Opcode: ABSQ_S_QB
/* 11639 */   MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 11652
/* 11643 */   MCD::OPC_CheckPredicate, 11, 170, 7, // Skip to: 13609
/* 11647 */   MCD::OPC_Decode, 219, 10, 197, 1, // Opcode: REPL_QB
/* 11652 */   MCD::OPC_FilterValue, 3, 15, 0, // Skip to: 11671
/* 11656 */   MCD::OPC_CheckPredicate, 11, 157, 7, // Skip to: 13609
/* 11660 */   MCD::OPC_CheckField, 21, 5, 0, 151, 7, // Skip to: 13609
/* 11666 */   MCD::OPC_Decode, 217, 10, 198, 1, // Opcode: REPLV_QB
/* 11671 */   MCD::OPC_FilterValue, 4, 15, 0, // Skip to: 11690
/* 11675 */   MCD::OPC_CheckPredicate, 11, 138, 7, // Skip to: 13609
/* 11679 */   MCD::OPC_CheckField, 21, 5, 0, 132, 7, // Skip to: 13609
/* 11685 */   MCD::OPC_Decode, 139, 10, 196, 1, // Opcode: PRECEQU_PH_QBL
/* 11690 */   MCD::OPC_FilterValue, 5, 15, 0, // Skip to: 11709
/* 11694 */   MCD::OPC_CheckPredicate, 11, 119, 7, // Skip to: 13609
/* 11698 */   MCD::OPC_CheckField, 21, 5, 0, 113, 7, // Skip to: 13609
/* 11704 */   MCD::OPC_Decode, 141, 10, 196, 1, // Opcode: PRECEQU_PH_QBR
/* 11709 */   MCD::OPC_FilterValue, 6, 15, 0, // Skip to: 11728
/* 11713 */   MCD::OPC_CheckPredicate, 11, 100, 7, // Skip to: 13609
/* 11717 */   MCD::OPC_CheckField, 21, 5, 0, 94, 7, // Skip to: 13609
/* 11723 */   MCD::OPC_Decode, 140, 10, 196, 1, // Opcode: PRECEQU_PH_QBLA
/* 11728 */   MCD::OPC_FilterValue, 7, 15, 0, // Skip to: 11747
/* 11732 */   MCD::OPC_CheckPredicate, 11, 81, 7, // Skip to: 13609
/* 11736 */   MCD::OPC_CheckField, 21, 5, 0, 75, 7, // Skip to: 13609
/* 11742 */   MCD::OPC_Decode, 142, 10, 196, 1, // Opcode: PRECEQU_PH_QBRA
/* 11747 */   MCD::OPC_FilterValue, 9, 14, 0, // Skip to: 11765
/* 11751 */   MCD::OPC_CheckPredicate, 11, 62, 7, // Skip to: 13609
/* 11755 */   MCD::OPC_CheckField, 21, 5, 0, 56, 7, // Skip to: 13609
/* 11761 */   MCD::OPC_Decode, 22, 196, 1, // Opcode: ABSQ_S_PH
/* 11765 */   MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 11778
/* 11769 */   MCD::OPC_CheckPredicate, 11, 44, 7, // Skip to: 13609
/* 11773 */   MCD::OPC_Decode, 218, 10, 197, 1, // Opcode: REPL_PH
/* 11778 */   MCD::OPC_FilterValue, 11, 15, 0, // Skip to: 11797
/* 11782 */   MCD::OPC_CheckPredicate, 11, 31, 7, // Skip to: 13609
/* 11786 */   MCD::OPC_CheckField, 21, 5, 0, 25, 7, // Skip to: 13609
/* 11792 */   MCD::OPC_Decode, 216, 10, 198, 1, // Opcode: REPLV_PH
/* 11797 */   MCD::OPC_FilterValue, 12, 15, 0, // Skip to: 11816
/* 11801 */   MCD::OPC_CheckPredicate, 11, 12, 7, // Skip to: 13609
/* 11805 */   MCD::OPC_CheckField, 21, 5, 0, 6, 7, // Skip to: 13609
/* 11811 */   MCD::OPC_Decode, 143, 10, 199, 1, // Opcode: PRECEQ_W_PHL
/* 11816 */   MCD::OPC_FilterValue, 13, 15, 0, // Skip to: 11835
/* 11820 */   MCD::OPC_CheckPredicate, 11, 249, 6, // Skip to: 13609
/* 11824 */   MCD::OPC_CheckField, 21, 5, 0, 243, 6, // Skip to: 13609
/* 11830 */   MCD::OPC_Decode, 144, 10, 199, 1, // Opcode: PRECEQ_W_PHR
/* 11835 */   MCD::OPC_FilterValue, 17, 14, 0, // Skip to: 11853
/* 11839 */   MCD::OPC_CheckPredicate, 11, 230, 6, // Skip to: 13609
/* 11843 */   MCD::OPC_CheckField, 21, 5, 0, 224, 6, // Skip to: 13609
/* 11849 */   MCD::OPC_Decode, 24, 200, 1, // Opcode: ABSQ_S_W
/* 11853 */   MCD::OPC_FilterValue, 27, 15, 0, // Skip to: 11872
/* 11857 */   MCD::OPC_CheckPredicate, 11, 212, 6, // Skip to: 13609
/* 11861 */   MCD::OPC_CheckField, 21, 5, 0, 206, 6, // Skip to: 13609
/* 11867 */   MCD::OPC_Decode, 231, 1, 200, 1, // Opcode: BITREV
/* 11872 */   MCD::OPC_FilterValue, 28, 15, 0, // Skip to: 11891
/* 11876 */   MCD::OPC_CheckPredicate, 11, 193, 6, // Skip to: 13609
/* 11880 */   MCD::OPC_CheckField, 21, 5, 0, 187, 6, // Skip to: 13609
/* 11886 */   MCD::OPC_Decode, 145, 10, 196, 1, // Opcode: PRECEU_PH_QBL
/* 11891 */   MCD::OPC_FilterValue, 29, 15, 0, // Skip to: 11910
/* 11895 */   MCD::OPC_CheckPredicate, 11, 174, 6, // Skip to: 13609
/* 11899 */   MCD::OPC_CheckField, 21, 5, 0, 168, 6, // Skip to: 13609
/* 11905 */   MCD::OPC_Decode, 147, 10, 196, 1, // Opcode: PRECEU_PH_QBR
/* 11910 */   MCD::OPC_FilterValue, 30, 15, 0, // Skip to: 11929
/* 11914 */   MCD::OPC_CheckPredicate, 11, 155, 6, // Skip to: 13609
/* 11918 */   MCD::OPC_CheckField, 21, 5, 0, 149, 6, // Skip to: 13609
/* 11924 */   MCD::OPC_Decode, 146, 10, 196, 1, // Opcode: PRECEU_PH_QBLA
/* 11929 */   MCD::OPC_FilterValue, 31, 140, 6, // Skip to: 13609
/* 11933 */   MCD::OPC_CheckPredicate, 11, 136, 6, // Skip to: 13609
/* 11937 */   MCD::OPC_CheckField, 21, 5, 0, 130, 6, // Skip to: 13609
/* 11943 */   MCD::OPC_Decode, 148, 10, 196, 1, // Opcode: PRECEU_PH_QBRA
/* 11948 */   MCD::OPC_FilterValue, 19, 31, 1, // Skip to: 12239
/* 11952 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 11955 */   MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 11968
/* 11959 */   MCD::OPC_CheckPredicate, 11, 110, 6, // Skip to: 13609
/* 11963 */   MCD::OPC_Decode, 174, 11, 201, 1, // Opcode: SHLL_QB
/* 11968 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 11981
/* 11972 */   MCD::OPC_CheckPredicate, 11, 97, 6, // Skip to: 13609
/* 11976 */   MCD::OPC_Decode, 190, 11, 201, 1, // Opcode: SHRL_QB
/* 11981 */   MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 11994
/* 11985 */   MCD::OPC_CheckPredicate, 11, 84, 6, // Skip to: 13609
/* 11989 */   MCD::OPC_Decode, 170, 11, 202, 1, // Opcode: SHLLV_QB
/* 11994 */   MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 12007
/* 11998 */   MCD::OPC_CheckPredicate, 11, 71, 6, // Skip to: 13609
/* 12002 */   MCD::OPC_Decode, 188, 11, 202, 1, // Opcode: SHRLV_QB
/* 12007 */   MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 12020
/* 12011 */   MCD::OPC_CheckPredicate, 29, 58, 6, // Skip to: 13609
/* 12015 */   MCD::OPC_Decode, 183, 11, 201, 1, // Opcode: SHRA_QB
/* 12020 */   MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 12033
/* 12024 */   MCD::OPC_CheckPredicate, 29, 45, 6, // Skip to: 13609
/* 12028 */   MCD::OPC_Decode, 185, 11, 201, 1, // Opcode: SHRA_R_QB
/* 12033 */   MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 12046
/* 12037 */   MCD::OPC_CheckPredicate, 29, 32, 6, // Skip to: 13609
/* 12041 */   MCD::OPC_Decode, 178, 11, 202, 1, // Opcode: SHRAV_QB
/* 12046 */   MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 12059
/* 12050 */   MCD::OPC_CheckPredicate, 29, 19, 6, // Skip to: 13609
/* 12054 */   MCD::OPC_Decode, 180, 11, 202, 1, // Opcode: SHRAV_R_QB
/* 12059 */   MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 12072
/* 12063 */   MCD::OPC_CheckPredicate, 11, 6, 6, // Skip to: 13609
/* 12067 */   MCD::OPC_Decode, 173, 11, 201, 1, // Opcode: SHLL_PH
/* 12072 */   MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 12085
/* 12076 */   MCD::OPC_CheckPredicate, 11, 249, 5, // Skip to: 13609
/* 12080 */   MCD::OPC_Decode, 182, 11, 201, 1, // Opcode: SHRA_PH
/* 12085 */   MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 12098
/* 12089 */   MCD::OPC_CheckPredicate, 11, 236, 5, // Skip to: 13609
/* 12093 */   MCD::OPC_Decode, 169, 11, 202, 1, // Opcode: SHLLV_PH
/* 12098 */   MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 12111
/* 12102 */   MCD::OPC_CheckPredicate, 11, 223, 5, // Skip to: 13609
/* 12106 */   MCD::OPC_Decode, 177, 11, 202, 1, // Opcode: SHRAV_PH
/* 12111 */   MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 12124
/* 12115 */   MCD::OPC_CheckPredicate, 11, 210, 5, // Skip to: 13609
/* 12119 */   MCD::OPC_Decode, 175, 11, 201, 1, // Opcode: SHLL_S_PH
/* 12124 */   MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 12137
/* 12128 */   MCD::OPC_CheckPredicate, 11, 197, 5, // Skip to: 13609
/* 12132 */   MCD::OPC_Decode, 184, 11, 201, 1, // Opcode: SHRA_R_PH
/* 12137 */   MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 12150
/* 12141 */   MCD::OPC_CheckPredicate, 11, 184, 5, // Skip to: 13609
/* 12145 */   MCD::OPC_Decode, 171, 11, 202, 1, // Opcode: SHLLV_S_PH
/* 12150 */   MCD::OPC_FilterValue, 15, 9, 0, // Skip to: 12163
/* 12154 */   MCD::OPC_CheckPredicate, 11, 171, 5, // Skip to: 13609
/* 12158 */   MCD::OPC_Decode, 179, 11, 202, 1, // Opcode: SHRAV_R_PH
/* 12163 */   MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 12176
/* 12167 */   MCD::OPC_CheckPredicate, 11, 158, 5, // Skip to: 13609
/* 12171 */   MCD::OPC_Decode, 176, 11, 203, 1, // Opcode: SHLL_S_W
/* 12176 */   MCD::OPC_FilterValue, 21, 9, 0, // Skip to: 12189
/* 12180 */   MCD::OPC_CheckPredicate, 11, 145, 5, // Skip to: 13609
/* 12184 */   MCD::OPC_Decode, 186, 11, 203, 1, // Opcode: SHRA_R_W
/* 12189 */   MCD::OPC_FilterValue, 22, 8, 0, // Skip to: 12201
/* 12193 */   MCD::OPC_CheckPredicate, 11, 132, 5, // Skip to: 13609
/* 12197 */   MCD::OPC_Decode, 172, 11, 33, // Opcode: SHLLV_S_W
/* 12201 */   MCD::OPC_FilterValue, 23, 8, 0, // Skip to: 12213
/* 12205 */   MCD::OPC_CheckPredicate, 11, 120, 5, // Skip to: 13609
/* 12209 */   MCD::OPC_Decode, 181, 11, 33, // Opcode: SHRAV_R_W
/* 12213 */   MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 12226
/* 12217 */   MCD::OPC_CheckPredicate, 29, 108, 5, // Skip to: 13609
/* 12221 */   MCD::OPC_Decode, 189, 11, 201, 1, // Opcode: SHRL_PH
/* 12226 */   MCD::OPC_FilterValue, 27, 99, 5, // Skip to: 13609
/* 12230 */   MCD::OPC_CheckPredicate, 29, 95, 5, // Skip to: 13609
/* 12234 */   MCD::OPC_Decode, 187, 11, 202, 1, // Opcode: SHRLV_PH
/* 12239 */   MCD::OPC_FilterValue, 24, 199, 0, // Skip to: 12442
/* 12243 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 12246 */   MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 12258
/* 12250 */   MCD::OPC_CheckPredicate, 29, 75, 5, // Skip to: 13609
/* 12254 */   MCD::OPC_Decode, 52, 190, 1, // Opcode: ADDUH_QB
/* 12258 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 12271
/* 12262 */   MCD::OPC_CheckPredicate, 29, 63, 5, // Skip to: 13609
/* 12266 */   MCD::OPC_Decode, 190, 12, 190, 1, // Opcode: SUBUH_QB
/* 12271 */   MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 12283
/* 12275 */   MCD::OPC_CheckPredicate, 29, 50, 5, // Skip to: 13609
/* 12279 */   MCD::OPC_Decode, 53, 190, 1, // Opcode: ADDUH_R_QB
/* 12283 */   MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 12296
/* 12287 */   MCD::OPC_CheckPredicate, 29, 38, 5, // Skip to: 13609
/* 12291 */   MCD::OPC_Decode, 191, 12, 190, 1, // Opcode: SUBUH_R_QB
/* 12296 */   MCD::OPC_FilterValue, 8, 8, 0, // Skip to: 12308
/* 12300 */   MCD::OPC_CheckPredicate, 29, 25, 5, // Skip to: 13609
/* 12304 */   MCD::OPC_Decode, 31, 190, 1, // Opcode: ADDQH_PH
/* 12308 */   MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 12321
/* 12312 */   MCD::OPC_CheckPredicate, 29, 13, 5, // Skip to: 13609
/* 12316 */   MCD::OPC_Decode, 166, 12, 190, 1, // Opcode: SUBQH_PH
/* 12321 */   MCD::OPC_FilterValue, 10, 8, 0, // Skip to: 12333
/* 12325 */   MCD::OPC_CheckPredicate, 29, 0, 5, // Skip to: 13609
/* 12329 */   MCD::OPC_Decode, 32, 190, 1, // Opcode: ADDQH_R_PH
/* 12333 */   MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 12346
/* 12337 */   MCD::OPC_CheckPredicate, 29, 244, 4, // Skip to: 13609
/* 12341 */   MCD::OPC_Decode, 167, 12, 190, 1, // Opcode: SUBQH_R_PH
/* 12346 */   MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 12359
/* 12350 */   MCD::OPC_CheckPredicate, 29, 231, 4, // Skip to: 13609
/* 12354 */   MCD::OPC_Decode, 193, 9, 190, 1, // Opcode: MUL_PH
/* 12359 */   MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 12372
/* 12363 */   MCD::OPC_CheckPredicate, 29, 218, 4, // Skip to: 13609
/* 12367 */   MCD::OPC_Decode, 197, 9, 190, 1, // Opcode: MUL_S_PH
/* 12372 */   MCD::OPC_FilterValue, 16, 7, 0, // Skip to: 12383
/* 12376 */   MCD::OPC_CheckPredicate, 29, 205, 4, // Skip to: 13609
/* 12380 */   MCD::OPC_Decode, 34, 32, // Opcode: ADDQH_W
/* 12383 */   MCD::OPC_FilterValue, 17, 8, 0, // Skip to: 12395
/* 12387 */   MCD::OPC_CheckPredicate, 29, 194, 4, // Skip to: 13609
/* 12391 */   MCD::OPC_Decode, 169, 12, 32, // Opcode: SUBQH_W
/* 12395 */   MCD::OPC_FilterValue, 18, 7, 0, // Skip to: 12406
/* 12399 */   MCD::OPC_CheckPredicate, 29, 182, 4, // Skip to: 13609
/* 12403 */   MCD::OPC_Decode, 33, 32, // Opcode: ADDQH_R_W
/* 12406 */   MCD::OPC_FilterValue, 19, 8, 0, // Skip to: 12418
/* 12410 */   MCD::OPC_CheckPredicate, 29, 171, 4, // Skip to: 13609
/* 12414 */   MCD::OPC_Decode, 168, 12, 32, // Opcode: SUBQH_R_W
/* 12418 */   MCD::OPC_FilterValue, 22, 8, 0, // Skip to: 12430
/* 12422 */   MCD::OPC_CheckPredicate, 29, 159, 4, // Skip to: 13609
/* 12426 */   MCD::OPC_Decode, 176, 9, 32, // Opcode: MULQ_S_W
/* 12430 */   MCD::OPC_FilterValue, 23, 151, 4, // Skip to: 13609
/* 12434 */   MCD::OPC_CheckPredicate, 29, 147, 4, // Skip to: 13609
/* 12438 */   MCD::OPC_Decode, 174, 9, 32, // Opcode: MULQ_RS_W
/* 12442 */   MCD::OPC_FilterValue, 32, 60, 0, // Skip to: 12506
/* 12446 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 12449 */   MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 12468
/* 12453 */   MCD::OPC_CheckPredicate, 4, 128, 4, // Skip to: 13609
/* 12457 */   MCD::OPC_CheckField, 21, 5, 0, 122, 4, // Skip to: 13609
/* 12463 */   MCD::OPC_Decode, 208, 13, 200, 1, // Opcode: WSBH
/* 12468 */   MCD::OPC_FilterValue, 16, 15, 0, // Skip to: 12487
/* 12472 */   MCD::OPC_CheckPredicate, 4, 109, 4, // Skip to: 13609
/* 12476 */   MCD::OPC_CheckField, 21, 5, 0, 103, 4, // Skip to: 13609
/* 12482 */   MCD::OPC_Decode, 143, 11, 200, 1, // Opcode: SEB
/* 12487 */   MCD::OPC_FilterValue, 24, 94, 4, // Skip to: 13609
/* 12491 */   MCD::OPC_CheckPredicate, 4, 90, 4, // Skip to: 13609
/* 12495 */   MCD::OPC_CheckField, 21, 5, 0, 84, 4, // Skip to: 13609
/* 12501 */   MCD::OPC_Decode, 146, 11, 200, 1, // Opcode: SEH
/* 12506 */   MCD::OPC_FilterValue, 48, 143, 1, // Skip to: 12909
/* 12510 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 12513 */   MCD::OPC_FilterValue, 0, 14, 0, // Skip to: 12531
/* 12517 */   MCD::OPC_CheckPredicate, 29, 64, 4, // Skip to: 13609
/* 12521 */   MCD::OPC_CheckField, 13, 3, 0, 58, 4, // Skip to: 13609
/* 12527 */   MCD::OPC_Decode, 211, 4, 111, // Opcode: DPA_W_PH
/* 12531 */   MCD::OPC_FilterValue, 1, 14, 0, // Skip to: 12549
/* 12535 */   MCD::OPC_CheckPredicate, 29, 46, 4, // Skip to: 13609
/* 12539 */   MCD::OPC_CheckField, 13, 3, 0, 40, 4, // Skip to: 13609
/* 12545 */   MCD::OPC_Decode, 226, 4, 111, // Opcode: DPS_W_PH
/* 12549 */   MCD::OPC_FilterValue, 2, 14, 0, // Skip to: 12567
/* 12553 */   MCD::OPC_CheckPredicate, 29, 28, 4, // Skip to: 13609
/* 12557 */   MCD::OPC_CheckField, 13, 3, 0, 22, 4, // Skip to: 13609
/* 12563 */   MCD::OPC_Decode, 180, 9, 111, // Opcode: MULSA_W_PH
/* 12567 */   MCD::OPC_FilterValue, 3, 14, 0, // Skip to: 12585
/* 12571 */   MCD::OPC_CheckPredicate, 11, 10, 4, // Skip to: 13609
/* 12575 */   MCD::OPC_CheckField, 13, 3, 0, 4, 4, // Skip to: 13609
/* 12581 */   MCD::OPC_Decode, 208, 4, 111, // Opcode: DPAU_H_QBL
/* 12585 */   MCD::OPC_FilterValue, 4, 14, 0, // Skip to: 12603
/* 12589 */   MCD::OPC_CheckPredicate, 11, 248, 3, // Skip to: 13609
/* 12593 */   MCD::OPC_CheckField, 13, 3, 0, 242, 3, // Skip to: 13609
/* 12599 */   MCD::OPC_Decode, 207, 4, 111, // Opcode: DPAQ_S_W_PH
/* 12603 */   MCD::OPC_FilterValue, 5, 14, 0, // Skip to: 12621
/* 12607 */   MCD::OPC_CheckPredicate, 11, 230, 3, // Skip to: 13609
/* 12611 */   MCD::OPC_CheckField, 13, 3, 0, 224, 3, // Skip to: 13609
/* 12617 */   MCD::OPC_Decode, 216, 4, 111, // Opcode: DPSQ_S_W_PH
/* 12621 */   MCD::OPC_FilterValue, 6, 14, 0, // Skip to: 12639
/* 12625 */   MCD::OPC_CheckPredicate, 11, 212, 3, // Skip to: 13609
/* 12629 */   MCD::OPC_CheckField, 13, 3, 0, 206, 3, // Skip to: 13609
/* 12635 */   MCD::OPC_Decode, 179, 9, 111, // Opcode: MULSAQ_S_W_PH
/* 12639 */   MCD::OPC_FilterValue, 7, 14, 0, // Skip to: 12657
/* 12643 */   MCD::OPC_CheckPredicate, 11, 194, 3, // Skip to: 13609
/* 12647 */   MCD::OPC_CheckField, 13, 3, 0, 188, 3, // Skip to: 13609
/* 12653 */   MCD::OPC_Decode, 209, 4, 111, // Opcode: DPAU_H_QBR
/* 12657 */   MCD::OPC_FilterValue, 8, 14, 0, // Skip to: 12675
/* 12661 */   MCD::OPC_CheckPredicate, 29, 176, 3, // Skip to: 13609
/* 12665 */   MCD::OPC_CheckField, 13, 3, 0, 170, 3, // Skip to: 13609
/* 12671 */   MCD::OPC_Decode, 210, 4, 111, // Opcode: DPAX_W_PH
/* 12675 */   MCD::OPC_FilterValue, 9, 14, 0, // Skip to: 12693
/* 12679 */   MCD::OPC_CheckPredicate, 29, 158, 3, // Skip to: 13609
/* 12683 */   MCD::OPC_CheckField, 13, 3, 0, 152, 3, // Skip to: 13609
/* 12689 */   MCD::OPC_Decode, 225, 4, 111, // Opcode: DPSX_W_PH
/* 12693 */   MCD::OPC_FilterValue, 11, 14, 0, // Skip to: 12711
/* 12697 */   MCD::OPC_CheckPredicate, 11, 140, 3, // Skip to: 13609
/* 12701 */   MCD::OPC_CheckField, 13, 3, 0, 134, 3, // Skip to: 13609
/* 12707 */   MCD::OPC_Decode, 223, 4, 111, // Opcode: DPSU_H_QBL
/* 12711 */   MCD::OPC_FilterValue, 12, 14, 0, // Skip to: 12729
/* 12715 */   MCD::OPC_CheckPredicate, 11, 122, 3, // Skip to: 13609
/* 12719 */   MCD::OPC_CheckField, 13, 3, 0, 116, 3, // Skip to: 13609
/* 12725 */   MCD::OPC_Decode, 206, 4, 111, // Opcode: DPAQ_SA_L_W
/* 12729 */   MCD::OPC_FilterValue, 13, 14, 0, // Skip to: 12747
/* 12733 */   MCD::OPC_CheckPredicate, 11, 104, 3, // Skip to: 13609
/* 12737 */   MCD::OPC_CheckField, 13, 3, 0, 98, 3, // Skip to: 13609
/* 12743 */   MCD::OPC_Decode, 215, 4, 111, // Opcode: DPSQ_SA_L_W
/* 12747 */   MCD::OPC_FilterValue, 15, 14, 0, // Skip to: 12765
/* 12751 */   MCD::OPC_CheckPredicate, 11, 86, 3, // Skip to: 13609
/* 12755 */   MCD::OPC_CheckField, 13, 3, 0, 80, 3, // Skip to: 13609
/* 12761 */   MCD::OPC_Decode, 224, 4, 111, // Opcode: DPSU_H_QBR
/* 12765 */   MCD::OPC_FilterValue, 16, 14, 0, // Skip to: 12783
/* 12769 */   MCD::OPC_CheckPredicate, 11, 68, 3, // Skip to: 13609
/* 12773 */   MCD::OPC_CheckField, 13, 3, 0, 62, 3, // Skip to: 13609
/* 12779 */   MCD::OPC_Decode, 255, 7, 111, // Opcode: MAQ_SA_W_PHL
/* 12783 */   MCD::OPC_FilterValue, 18, 14, 0, // Skip to: 12801
/* 12787 */   MCD::OPC_CheckPredicate, 11, 50, 3, // Skip to: 13609
/* 12791 */   MCD::OPC_CheckField, 13, 3, 0, 44, 3, // Skip to: 13609
/* 12797 */   MCD::OPC_Decode, 128, 8, 111, // Opcode: MAQ_SA_W_PHR
/* 12801 */   MCD::OPC_FilterValue, 20, 14, 0, // Skip to: 12819
/* 12805 */   MCD::OPC_CheckPredicate, 11, 32, 3, // Skip to: 13609
/* 12809 */   MCD::OPC_CheckField, 13, 3, 0, 26, 3, // Skip to: 13609
/* 12815 */   MCD::OPC_Decode, 129, 8, 111, // Opcode: MAQ_S_W_PHL
/* 12819 */   MCD::OPC_FilterValue, 22, 14, 0, // Skip to: 12837
/* 12823 */   MCD::OPC_CheckPredicate, 11, 14, 3, // Skip to: 13609
/* 12827 */   MCD::OPC_CheckField, 13, 3, 0, 8, 3, // Skip to: 13609
/* 12833 */   MCD::OPC_Decode, 130, 8, 111, // Opcode: MAQ_S_W_PHR
/* 12837 */   MCD::OPC_FilterValue, 24, 14, 0, // Skip to: 12855
/* 12841 */   MCD::OPC_CheckPredicate, 29, 252, 2, // Skip to: 13609
/* 12845 */   MCD::OPC_CheckField, 13, 3, 0, 246, 2, // Skip to: 13609
/* 12851 */   MCD::OPC_Decode, 205, 4, 111, // Opcode: DPAQX_S_W_PH
/* 12855 */   MCD::OPC_FilterValue, 25, 14, 0, // Skip to: 12873
/* 12859 */   MCD::OPC_CheckPredicate, 29, 234, 2, // Skip to: 13609
/* 12863 */   MCD::OPC_CheckField, 13, 3, 0, 228, 2, // Skip to: 13609
/* 12869 */   MCD::OPC_Decode, 214, 4, 111, // Opcode: DPSQX_S_W_PH
/* 12873 */   MCD::OPC_FilterValue, 26, 14, 0, // Skip to: 12891
/* 12877 */   MCD::OPC_CheckPredicate, 29, 216, 2, // Skip to: 13609
/* 12881 */   MCD::OPC_CheckField, 13, 3, 0, 210, 2, // Skip to: 13609
/* 12887 */   MCD::OPC_Decode, 204, 4, 111, // Opcode: DPAQX_SA_W_PH
/* 12891 */   MCD::OPC_FilterValue, 27, 202, 2, // Skip to: 13609
/* 12895 */   MCD::OPC_CheckPredicate, 29, 198, 2, // Skip to: 13609
/* 12899 */   MCD::OPC_CheckField, 13, 3, 0, 192, 2, // Skip to: 13609
/* 12905 */   MCD::OPC_Decode, 213, 4, 111, // Opcode: DPSQX_SA_W_PH
/* 12909 */   MCD::OPC_FilterValue, 49, 41, 0, // Skip to: 12954
/* 12913 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 12916 */   MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 12928
/* 12920 */   MCD::OPC_CheckPredicate, 29, 173, 2, // Skip to: 13609
/* 12924 */   MCD::OPC_Decode, 95, 204, 1, // Opcode: APPEND
/* 12928 */   MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 12941
/* 12932 */   MCD::OPC_CheckPredicate, 29, 161, 2, // Skip to: 13609
/* 12936 */   MCD::OPC_Decode, 159, 10, 204, 1, // Opcode: PREPEND
/* 12941 */   MCD::OPC_FilterValue, 16, 152, 2, // Skip to: 13609
/* 12945 */   MCD::OPC_CheckPredicate, 29, 148, 2, // Skip to: 13609
/* 12949 */   MCD::OPC_Decode, 167, 1, 204, 1, // Opcode: BALIGN
/* 12954 */   MCD::OPC_FilterValue, 56, 58, 1, // Skip to: 13272
/* 12958 */   MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 12961 */   MCD::OPC_FilterValue, 0, 15, 0, // Skip to: 12980
/* 12965 */   MCD::OPC_CheckPredicate, 11, 128, 2, // Skip to: 13609
/* 12969 */   MCD::OPC_CheckField, 13, 3, 0, 122, 2, // Skip to: 13609
/* 12975 */   MCD::OPC_Decode, 138, 5, 205, 1, // Opcode: EXTR_W
/* 12980 */   MCD::OPC_FilterValue, 1, 15, 0, // Skip to: 12999
/* 12984 */   MCD::OPC_CheckPredicate, 11, 109, 2, // Skip to: 13609
/* 12988 */   MCD::OPC_CheckField, 13, 3, 0, 103, 2, // Skip to: 13609
/* 12994 */   MCD::OPC_Decode, 134, 5, 206, 1, // Opcode: EXTRV_W
/* 12999 */   MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 13018
/* 13003 */   MCD::OPC_CheckPredicate, 11, 90, 2, // Skip to: 13609
/* 13007 */   MCD::OPC_CheckField, 13, 3, 0, 84, 2, // Skip to: 13609
/* 13013 */   MCD::OPC_Decode, 255, 4, 205, 1, // Opcode: EXTP
/* 13018 */   MCD::OPC_FilterValue, 3, 15, 0, // Skip to: 13037
/* 13022 */   MCD::OPC_CheckPredicate, 11, 71, 2, // Skip to: 13609
/* 13026 */   MCD::OPC_CheckField, 13, 3, 0, 65, 2, // Skip to: 13609
/* 13032 */   MCD::OPC_Decode, 130, 5, 206, 1, // Opcode: EXTPV
/* 13037 */   MCD::OPC_FilterValue, 4, 15, 0, // Skip to: 13056
/* 13041 */   MCD::OPC_CheckPredicate, 11, 52, 2, // Skip to: 13609
/* 13045 */   MCD::OPC_CheckField, 13, 3, 0, 46, 2, // Skip to: 13609
/* 13051 */   MCD::OPC_Decode, 136, 5, 205, 1, // Opcode: EXTR_R_W
/* 13056 */   MCD::OPC_FilterValue, 5, 15, 0, // Skip to: 13075
/* 13060 */   MCD::OPC_CheckPredicate, 11, 33, 2, // Skip to: 13609
/* 13064 */   MCD::OPC_CheckField, 13, 3, 0, 27, 2, // Skip to: 13609
/* 13070 */   MCD::OPC_Decode, 132, 5, 206, 1, // Opcode: EXTRV_R_W
/* 13075 */   MCD::OPC_FilterValue, 6, 15, 0, // Skip to: 13094
/* 13079 */   MCD::OPC_CheckPredicate, 11, 14, 2, // Skip to: 13609
/* 13083 */   MCD::OPC_CheckField, 13, 3, 0, 8, 2, // Skip to: 13609
/* 13089 */   MCD::OPC_Decode, 135, 5, 205, 1, // Opcode: EXTR_RS_W
/* 13094 */   MCD::OPC_FilterValue, 7, 15, 0, // Skip to: 13113
/* 13098 */   MCD::OPC_CheckPredicate, 11, 251, 1, // Skip to: 13609
/* 13102 */   MCD::OPC_CheckField, 13, 3, 0, 245, 1, // Skip to: 13609
/* 13108 */   MCD::OPC_Decode, 131, 5, 206, 1, // Opcode: EXTRV_RS_W
/* 13113 */   MCD::OPC_FilterValue, 10, 15, 0, // Skip to: 13132
/* 13117 */   MCD::OPC_CheckPredicate, 11, 232, 1, // Skip to: 13609
/* 13121 */   MCD::OPC_CheckField, 13, 3, 0, 226, 1, // Skip to: 13609
/* 13127 */   MCD::OPC_Decode, 128, 5, 205, 1, // Opcode: EXTPDP
/* 13132 */   MCD::OPC_FilterValue, 11, 15, 0, // Skip to: 13151
/* 13136 */   MCD::OPC_CheckPredicate, 11, 213, 1, // Skip to: 13609
/* 13140 */   MCD::OPC_CheckField, 13, 3, 0, 207, 1, // Skip to: 13609
/* 13146 */   MCD::OPC_Decode, 129, 5, 206, 1, // Opcode: EXTPDPV
/* 13151 */   MCD::OPC_FilterValue, 14, 15, 0, // Skip to: 13170
/* 13155 */   MCD::OPC_CheckPredicate, 11, 194, 1, // Skip to: 13609
/* 13159 */   MCD::OPC_CheckField, 13, 3, 0, 188, 1, // Skip to: 13609
/* 13165 */   MCD::OPC_Decode, 137, 5, 205, 1, // Opcode: EXTR_S_H
/* 13170 */   MCD::OPC_FilterValue, 15, 15, 0, // Skip to: 13189
/* 13174 */   MCD::OPC_CheckPredicate, 11, 175, 1, // Skip to: 13609
/* 13178 */   MCD::OPC_CheckField, 13, 3, 0, 169, 1, // Skip to: 13609
/* 13184 */   MCD::OPC_Decode, 133, 5, 206, 1, // Opcode: EXTRV_S_H
/* 13189 */   MCD::OPC_FilterValue, 18, 9, 0, // Skip to: 13202
/* 13193 */   MCD::OPC_CheckPredicate, 11, 156, 1, // Skip to: 13609
/* 13197 */   MCD::OPC_Decode, 212, 10, 207, 1, // Opcode: RDDSP
/* 13202 */   MCD::OPC_FilterValue, 19, 9, 0, // Skip to: 13215
/* 13206 */   MCD::OPC_CheckPredicate, 11, 143, 1, // Skip to: 13609
/* 13210 */   MCD::OPC_Decode, 207, 13, 208, 1, // Opcode: WRDSP
/* 13215 */   MCD::OPC_FilterValue, 26, 15, 0, // Skip to: 13234
/* 13219 */   MCD::OPC_CheckPredicate, 11, 130, 1, // Skip to: 13609
/* 13223 */   MCD::OPC_CheckField, 13, 7, 0, 124, 1, // Skip to: 13609
/* 13229 */   MCD::OPC_Decode, 167, 11, 209, 1, // Opcode: SHILO
/* 13234 */   MCD::OPC_FilterValue, 27, 15, 0, // Skip to: 13253
/* 13238 */   MCD::OPC_CheckPredicate, 11, 111, 1, // Skip to: 13609
/* 13242 */   MCD::OPC_CheckField, 13, 8, 0, 105, 1, // Skip to: 13609
/* 13248 */   MCD::OPC_Decode, 168, 11, 210, 1, // Opcode: SHILOV
/* 13253 */   MCD::OPC_FilterValue, 31, 96, 1, // Skip to: 13609
/* 13257 */   MCD::OPC_CheckPredicate, 11, 92, 1, // Skip to: 13609
/* 13261 */   MCD::OPC_CheckField, 13, 8, 0, 86, 1, // Skip to: 13609
/* 13267 */   MCD::OPC_Decode, 155, 9, 210, 1, // Opcode: MTHLIP
/* 13272 */   MCD::OPC_FilterValue, 59, 77, 1, // Skip to: 13609
/* 13276 */   MCD::OPC_CheckPredicate, 1, 73, 1, // Skip to: 13609
/* 13280 */   MCD::OPC_CheckField, 21, 5, 0, 67, 1, // Skip to: 13609
/* 13286 */   MCD::OPC_CheckField, 6, 5, 0, 61, 1, // Skip to: 13609
/* 13292 */   MCD::OPC_Decode, 213, 10, 211, 1, // Opcode: RDHWR
/* 13297 */   MCD::OPC_FilterValue, 32, 9, 0, // Skip to: 13310
/* 13301 */   MCD::OPC_CheckPredicate, 1, 48, 1, // Skip to: 13609
/* 13305 */   MCD::OPC_Decode, 131, 7, 212, 1, // Opcode: LB
/* 13310 */   MCD::OPC_FilterValue, 33, 9, 0, // Skip to: 13323
/* 13314 */   MCD::OPC_CheckPredicate, 1, 35, 1, // Skip to: 13609
/* 13318 */   MCD::OPC_Decode, 162, 7, 212, 1, // Opcode: LH
/* 13323 */   MCD::OPC_FilterValue, 34, 9, 0, // Skip to: 13336
/* 13327 */   MCD::OPC_CheckPredicate, 10, 22, 1, // Skip to: 13609
/* 13331 */   MCD::OPC_Decode, 199, 7, 212, 1, // Opcode: LWL
/* 13336 */   MCD::OPC_FilterValue, 35, 9, 0, // Skip to: 13349
/* 13340 */   MCD::OPC_CheckPredicate, 1, 9, 1, // Skip to: 13609
/* 13344 */   MCD::OPC_Decode, 191, 7, 212, 1, // Opcode: LW
/* 13349 */   MCD::OPC_FilterValue, 36, 9, 0, // Skip to: 13362
/* 13353 */   MCD::OPC_CheckPredicate, 1, 252, 0, // Skip to: 13609
/* 13357 */   MCD::OPC_Decode, 136, 7, 212, 1, // Opcode: LBu
/* 13362 */   MCD::OPC_FilterValue, 37, 9, 0, // Skip to: 13375
/* 13366 */   MCD::OPC_CheckPredicate, 1, 239, 0, // Skip to: 13609
/* 13370 */   MCD::OPC_Decode, 167, 7, 212, 1, // Opcode: LHu
/* 13375 */   MCD::OPC_FilterValue, 38, 9, 0, // Skip to: 13388
/* 13379 */   MCD::OPC_CheckPredicate, 10, 226, 0, // Skip to: 13609
/* 13383 */   MCD::OPC_Decode, 206, 7, 212, 1, // Opcode: LWR
/* 13388 */   MCD::OPC_FilterValue, 40, 9, 0, // Skip to: 13401
/* 13392 */   MCD::OPC_CheckPredicate, 1, 213, 0, // Skip to: 13609
/* 13396 */   MCD::OPC_Decode, 245, 10, 212, 1, // Opcode: SB
/* 13401 */   MCD::OPC_FilterValue, 41, 9, 0, // Skip to: 13414
/* 13405 */   MCD::OPC_CheckPredicate, 1, 200, 0, // Skip to: 13609
/* 13409 */   MCD::OPC_Decode, 161, 11, 212, 1, // Opcode: SH
/* 13414 */   MCD::OPC_FilterValue, 42, 9, 0, // Skip to: 13427
/* 13418 */   MCD::OPC_CheckPredicate, 10, 187, 0, // Skip to: 13609
/* 13422 */   MCD::OPC_Decode, 218, 12, 212, 1, // Opcode: SWL
/* 13427 */   MCD::OPC_FilterValue, 43, 9, 0, // Skip to: 13440
/* 13431 */   MCD::OPC_CheckPredicate, 1, 174, 0, // Skip to: 13609
/* 13435 */   MCD::OPC_Decode, 210, 12, 212, 1, // Opcode: SW
/* 13440 */   MCD::OPC_FilterValue, 46, 9, 0, // Skip to: 13453
/* 13444 */   MCD::OPC_CheckPredicate, 10, 161, 0, // Skip to: 13609
/* 13448 */   MCD::OPC_Decode, 224, 12, 212, 1, // Opcode: SWR
/* 13453 */   MCD::OPC_FilterValue, 47, 9, 0, // Skip to: 13466
/* 13457 */   MCD::OPC_CheckPredicate, 30, 148, 0, // Skip to: 13609
/* 13461 */   MCD::OPC_Decode, 201, 2, 213, 1, // Opcode: CACHE
/* 13466 */   MCD::OPC_FilterValue, 48, 9, 0, // Skip to: 13479
/* 13470 */   MCD::OPC_CheckPredicate, 31, 135, 0, // Skip to: 13609
/* 13474 */   MCD::OPC_Decode, 171, 7, 212, 1, // Opcode: LL
/* 13479 */   MCD::OPC_FilterValue, 49, 9, 0, // Skip to: 13492
/* 13483 */   MCD::OPC_CheckPredicate, 1, 122, 0, // Skip to: 13609
/* 13487 */   MCD::OPC_Decode, 194, 7, 214, 1, // Opcode: LWC1
/* 13492 */   MCD::OPC_FilterValue, 50, 9, 0, // Skip to: 13505
/* 13496 */   MCD::OPC_CheckPredicate, 12, 109, 0, // Skip to: 13609
/* 13500 */   MCD::OPC_Decode, 196, 7, 215, 1, // Opcode: LWC2
/* 13505 */   MCD::OPC_FilterValue, 51, 9, 0, // Skip to: 13518
/* 13509 */   MCD::OPC_CheckPredicate, 30, 96, 0, // Skip to: 13609
/* 13513 */   MCD::OPC_Decode, 156, 10, 213, 1, // Opcode: PREF
/* 13518 */   MCD::OPC_FilterValue, 53, 9, 0, // Skip to: 13531
/* 13522 */   MCD::OPC_CheckPredicate, 32, 83, 0, // Skip to: 13609
/* 13526 */   MCD::OPC_Decode, 140, 7, 214, 1, // Opcode: LDC1
/* 13531 */   MCD::OPC_FilterValue, 54, 9, 0, // Skip to: 13544
/* 13535 */   MCD::OPC_CheckPredicate, 14, 70, 0, // Skip to: 13609
/* 13539 */   MCD::OPC_Decode, 143, 7, 215, 1, // Opcode: LDC2
/* 13544 */   MCD::OPC_FilterValue, 56, 9, 0, // Skip to: 13557
/* 13548 */   MCD::OPC_CheckPredicate, 31, 57, 0, // Skip to: 13609
/* 13552 */   MCD::OPC_Decode, 249, 10, 212, 1, // Opcode: SC
/* 13557 */   MCD::OPC_FilterValue, 57, 9, 0, // Skip to: 13570
/* 13561 */   MCD::OPC_CheckPredicate, 1, 44, 0, // Skip to: 13609
/* 13565 */   MCD::OPC_Decode, 213, 12, 214, 1, // Opcode: SWC1
/* 13570 */   MCD::OPC_FilterValue, 58, 9, 0, // Skip to: 13583
/* 13574 */   MCD::OPC_CheckPredicate, 12, 31, 0, // Skip to: 13609
/* 13578 */   MCD::OPC_Decode, 215, 12, 215, 1, // Opcode: SWC2
/* 13583 */   MCD::OPC_FilterValue, 61, 9, 0, // Skip to: 13596
/* 13587 */   MCD::OPC_CheckPredicate, 32, 18, 0, // Skip to: 13609
/* 13591 */   MCD::OPC_Decode, 131, 11, 214, 1, // Opcode: SDC1
/* 13596 */   MCD::OPC_FilterValue, 62, 9, 0, // Skip to: 13609
/* 13600 */   MCD::OPC_CheckPredicate, 14, 5, 0, // Skip to: 13609
/* 13604 */   MCD::OPC_Decode, 134, 11, 215, 1, // Opcode: SDC2
/* 13609 */   MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMips32r6_64r632[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 0, 205, 1, // Skip to: 468
/* 7 */       MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 10 */      MCD::OPC_FilterValue, 5, 15, 0, // Skip to: 29
/* 14 */      MCD::OPC_CheckPredicate, 33, 39, 7, // Skip to: 1849
/* 18 */      MCD::OPC_CheckField, 8, 3, 0, 33, 7, // Skip to: 1849
/* 24 */      MCD::OPC_Decode, 184, 7, 216, 1, // Opcode: LSA_R6
/* 29 */      MCD::OPC_FilterValue, 9, 14, 0, // Skip to: 47
/* 33 */      MCD::OPC_CheckPredicate, 33, 20, 7, // Skip to: 1849
/* 37 */      MCD::OPC_CheckField, 6, 15, 16, 14, 7, // Skip to: 1849
/* 43 */      MCD::OPC_Decode, 250, 6, 57, // Opcode: JR_HB_R6
/* 47 */      MCD::OPC_FilterValue, 14, 8, 0, // Skip to: 59
/* 51 */      MCD::OPC_CheckPredicate, 33, 2, 7, // Skip to: 1849
/* 55 */      MCD::OPC_Decode, 130, 11, 60, // Opcode: SDBBP_R6
/* 59 */      MCD::OPC_FilterValue, 16, 20, 0, // Skip to: 83
/* 63 */      MCD::OPC_CheckPredicate, 33, 246, 6, // Skip to: 1849
/* 67 */      MCD::OPC_CheckField, 16, 5, 0, 240, 6, // Skip to: 1849
/* 73 */      MCD::OPC_CheckField, 6, 5, 1, 234, 6, // Skip to: 1849
/* 79 */      MCD::OPC_Decode, 135, 3, 58, // Opcode: CLZ_R6
/* 83 */      MCD::OPC_FilterValue, 17, 20, 0, // Skip to: 107
/* 87 */      MCD::OPC_CheckPredicate, 33, 222, 6, // Skip to: 1849
/* 91 */      MCD::OPC_CheckField, 16, 5, 0, 216, 6, // Skip to: 1849
/* 97 */      MCD::OPC_CheckField, 6, 5, 1, 210, 6, // Skip to: 1849
/* 103 */     MCD::OPC_Decode, 244, 2, 58, // Opcode: CLO_R6
/* 107 */     MCD::OPC_FilterValue, 18, 21, 0, // Skip to: 132
/* 111 */     MCD::OPC_CheckPredicate, 34, 198, 6, // Skip to: 1849
/* 115 */     MCD::OPC_CheckField, 16, 5, 0, 192, 6, // Skip to: 1849
/* 121 */     MCD::OPC_CheckField, 6, 5, 1, 186, 6, // Skip to: 1849
/* 127 */     MCD::OPC_Decode, 152, 4, 217, 1, // Opcode: DCLZ_R6
/* 132 */     MCD::OPC_FilterValue, 19, 21, 0, // Skip to: 157
/* 136 */     MCD::OPC_CheckPredicate, 34, 173, 6, // Skip to: 1849
/* 140 */     MCD::OPC_CheckField, 16, 5, 0, 167, 6, // Skip to: 1849
/* 146 */     MCD::OPC_CheckField, 6, 5, 1, 161, 6, // Skip to: 1849
/* 152 */     MCD::OPC_Decode, 150, 4, 217, 1, // Opcode: DCLO_R6
/* 157 */     MCD::OPC_FilterValue, 21, 15, 0, // Skip to: 176
/* 161 */     MCD::OPC_CheckPredicate, 34, 148, 6, // Skip to: 1849
/* 165 */     MCD::OPC_CheckField, 8, 3, 0, 142, 6, // Skip to: 1849
/* 171 */     MCD::OPC_Decode, 176, 4, 218, 1, // Opcode: DLSA_R6
/* 176 */     MCD::OPC_FilterValue, 24, 27, 0, // Skip to: 207
/* 180 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 183 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 195
/* 187 */     MCD::OPC_CheckPredicate, 33, 122, 6, // Skip to: 1849
/* 191 */     MCD::OPC_Decode, 196, 9, 32, // Opcode: MUL_R6
/* 195 */     MCD::OPC_FilterValue, 3, 114, 6, // Skip to: 1849
/* 199 */     MCD::OPC_CheckPredicate, 33, 110, 6, // Skip to: 1849
/* 203 */     MCD::OPC_Decode, 166, 9, 32, // Opcode: MUH
/* 207 */     MCD::OPC_FilterValue, 25, 27, 0, // Skip to: 238
/* 211 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 214 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 226
/* 218 */     MCD::OPC_CheckPredicate, 33, 91, 6, // Skip to: 1849
/* 222 */     MCD::OPC_Decode, 187, 9, 32, // Opcode: MULU
/* 226 */     MCD::OPC_FilterValue, 3, 83, 6, // Skip to: 1849
/* 230 */     MCD::OPC_CheckPredicate, 33, 79, 6, // Skip to: 1849
/* 234 */     MCD::OPC_Decode, 167, 9, 32, // Opcode: MUHU
/* 238 */     MCD::OPC_FilterValue, 26, 27, 0, // Skip to: 269
/* 242 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 245 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 257
/* 249 */     MCD::OPC_CheckPredicate, 33, 60, 6, // Skip to: 1849
/* 253 */     MCD::OPC_Decode, 164, 4, 32, // Opcode: DIV
/* 257 */     MCD::OPC_FilterValue, 3, 52, 6, // Skip to: 1849
/* 261 */     MCD::OPC_CheckPredicate, 33, 48, 6, // Skip to: 1849
/* 265 */     MCD::OPC_Decode, 198, 8, 32, // Opcode: MOD
/* 269 */     MCD::OPC_FilterValue, 27, 27, 0, // Skip to: 300
/* 273 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 276 */     MCD::OPC_FilterValue, 2, 8, 0, // Skip to: 288
/* 280 */     MCD::OPC_CheckPredicate, 33, 29, 6, // Skip to: 1849
/* 284 */     MCD::OPC_Decode, 165, 4, 32, // Opcode: DIVU
/* 288 */     MCD::OPC_FilterValue, 3, 21, 6, // Skip to: 1849
/* 292 */     MCD::OPC_CheckPredicate, 33, 17, 6, // Skip to: 1849
/* 296 */     MCD::OPC_Decode, 200, 8, 32, // Opcode: MODU
/* 300 */     MCD::OPC_FilterValue, 28, 29, 0, // Skip to: 333
/* 304 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 307 */     MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 320
/* 311 */     MCD::OPC_CheckPredicate, 34, 254, 5, // Skip to: 1849
/* 315 */     MCD::OPC_Decode, 191, 4, 219, 1, // Opcode: DMUL_R6
/* 320 */     MCD::OPC_FilterValue, 3, 245, 5, // Skip to: 1849
/* 324 */     MCD::OPC_CheckPredicate, 34, 241, 5, // Skip to: 1849
/* 328 */     MCD::OPC_Decode, 185, 4, 219, 1, // Opcode: DMUH
/* 333 */     MCD::OPC_FilterValue, 29, 29, 0, // Skip to: 366
/* 337 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 340 */     MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 353
/* 344 */     MCD::OPC_CheckPredicate, 34, 221, 5, // Skip to: 1849
/* 348 */     MCD::OPC_Decode, 190, 4, 219, 1, // Opcode: DMULU
/* 353 */     MCD::OPC_FilterValue, 3, 212, 5, // Skip to: 1849
/* 357 */     MCD::OPC_CheckPredicate, 34, 208, 5, // Skip to: 1849
/* 361 */     MCD::OPC_Decode, 186, 4, 219, 1, // Opcode: DMUHU
/* 366 */     MCD::OPC_FilterValue, 30, 29, 0, // Skip to: 399
/* 370 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 373 */     MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 386
/* 377 */     MCD::OPC_CheckPredicate, 34, 188, 5, // Skip to: 1849
/* 381 */     MCD::OPC_Decode, 153, 4, 219, 1, // Opcode: DDIV
/* 386 */     MCD::OPC_FilterValue, 3, 179, 5, // Skip to: 1849
/* 390 */     MCD::OPC_CheckPredicate, 34, 175, 5, // Skip to: 1849
/* 394 */     MCD::OPC_Decode, 180, 4, 219, 1, // Opcode: DMOD
/* 399 */     MCD::OPC_FilterValue, 31, 29, 0, // Skip to: 432
/* 403 */     MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 406 */     MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 419
/* 410 */     MCD::OPC_CheckPredicate, 34, 155, 5, // Skip to: 1849
/* 414 */     MCD::OPC_Decode, 154, 4, 219, 1, // Opcode: DDIVU
/* 419 */     MCD::OPC_FilterValue, 3, 146, 5, // Skip to: 1849
/* 423 */     MCD::OPC_CheckPredicate, 34, 142, 5, // Skip to: 1849
/* 427 */     MCD::OPC_Decode, 181, 4, 219, 1, // Opcode: DMODU
/* 432 */     MCD::OPC_FilterValue, 53, 14, 0, // Skip to: 450
/* 436 */     MCD::OPC_CheckPredicate, 35, 129, 5, // Skip to: 1849
/* 440 */     MCD::OPC_CheckField, 6, 5, 0, 123, 5, // Skip to: 1849
/* 446 */     MCD::OPC_Decode, 149, 11, 32, // Opcode: SELEQZ
/* 450 */     MCD::OPC_FilterValue, 55, 115, 5, // Skip to: 1849
/* 454 */     MCD::OPC_CheckPredicate, 35, 111, 5, // Skip to: 1849
/* 458 */     MCD::OPC_CheckField, 6, 5, 0, 105, 5, // Skip to: 1849
/* 464 */     MCD::OPC_Decode, 153, 11, 32, // Opcode: SELNEZ
/* 468 */     MCD::OPC_FilterValue, 1, 47, 0, // Skip to: 519
/* 472 */     MCD::OPC_ExtractField, 16, 5,  // Inst{20-16} ...
/* 475 */     MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 488
/* 479 */     MCD::OPC_CheckPredicate, 34, 86, 5, // Skip to: 1849
/* 483 */     MCD::OPC_Decode, 144, 4, 220, 1, // Opcode: DAHI
/* 488 */     MCD::OPC_FilterValue, 17, 14, 0, // Skip to: 506
/* 492 */     MCD::OPC_CheckPredicate, 33, 73, 5, // Skip to: 1849
/* 496 */     MCD::OPC_CheckField, 21, 5, 0, 67, 5, // Skip to: 1849
/* 502 */     MCD::OPC_Decode, 165, 1, 71, // Opcode: BAL
/* 506 */     MCD::OPC_FilterValue, 30, 59, 5, // Skip to: 1849
/* 510 */     MCD::OPC_CheckPredicate, 34, 55, 5, // Skip to: 1849
/* 514 */     MCD::OPC_Decode, 146, 4, 220, 1, // Opcode: DATI
/* 519 */     MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 532
/* 523 */     MCD::OPC_CheckPredicate, 33, 42, 5, // Skip to: 1849
/* 527 */     MCD::OPC_Decode, 202, 1, 221, 1, // Opcode: BGEZALC
/* 532 */     MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 545
/* 536 */     MCD::OPC_CheckPredicate, 33, 29, 5, // Skip to: 1849
/* 540 */     MCD::OPC_Decode, 244, 1, 222, 1, // Opcode: BLTZALC
/* 545 */     MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 558
/* 549 */     MCD::OPC_CheckPredicate, 33, 16, 5, // Skip to: 1849
/* 553 */     MCD::OPC_Decode, 190, 1, 223, 1, // Opcode: BEQC
/* 558 */     MCD::OPC_FilterValue, 15, 8, 0, // Skip to: 570
/* 562 */     MCD::OPC_CheckPredicate, 33, 3, 5, // Skip to: 1849
/* 566 */     MCD::OPC_Decode, 136, 1, 44, // Opcode: AUI
/* 570 */     MCD::OPC_FilterValue, 17, 5, 3, // Skip to: 1347
/* 574 */     MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 577 */     MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 590
/* 581 */     MCD::OPC_CheckPredicate, 33, 240, 4, // Skip to: 1849
/* 585 */     MCD::OPC_Decode, 170, 1, 224, 1, // Opcode: BC1EQZ
/* 590 */     MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 603
/* 594 */     MCD::OPC_CheckPredicate, 33, 227, 4, // Skip to: 1849
/* 598 */     MCD::OPC_Decode, 174, 1, 224, 1, // Opcode: BC1NEZ
/* 603 */     MCD::OPC_FilterValue, 16, 150, 0, // Skip to: 757
/* 607 */     MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 610 */     MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 623
/* 614 */     MCD::OPC_CheckPredicate, 33, 207, 4, // Skip to: 1849
/* 618 */     MCD::OPC_Decode, 158, 11, 225, 1, // Opcode: SEL_S
/* 623 */     MCD::OPC_FilterValue, 20, 8, 0, // Skip to: 635
/* 627 */     MCD::OPC_CheckPredicate, 33, 194, 4, // Skip to: 1849
/* 631 */     MCD::OPC_Decode, 152, 11, 88, // Opcode: SELEQZ_S
/* 635 */     MCD::OPC_FilterValue, 23, 8, 0, // Skip to: 647
/* 639 */     MCD::OPC_CheckPredicate, 33, 182, 4, // Skip to: 1849
/* 643 */     MCD::OPC_Decode, 156, 11, 88, // Opcode: SELNEZ_S
/* 647 */     MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 660
/* 651 */     MCD::OPC_CheckPredicate, 33, 170, 4, // Skip to: 1849
/* 655 */     MCD::OPC_Decode, 236, 7, 226, 1, // Opcode: MADDF_S
/* 660 */     MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 673
/* 664 */     MCD::OPC_CheckPredicate, 33, 157, 4, // Skip to: 1849
/* 668 */     MCD::OPC_Decode, 253, 8, 226, 1, // Opcode: MSUBF_S
/* 673 */     MCD::OPC_FilterValue, 26, 14, 0, // Skip to: 691
/* 677 */     MCD::OPC_CheckPredicate, 33, 144, 4, // Skip to: 1849
/* 681 */     MCD::OPC_CheckField, 16, 5, 0, 138, 4, // Skip to: 1849
/* 687 */     MCD::OPC_Decode, 221, 10, 89, // Opcode: RINT_S
/* 691 */     MCD::OPC_FilterValue, 27, 14, 0, // Skip to: 709
/* 695 */     MCD::OPC_CheckPredicate, 33, 126, 4, // Skip to: 1849
/* 699 */     MCD::OPC_CheckField, 16, 5, 0, 120, 4, // Skip to: 1849
/* 705 */     MCD::OPC_Decode, 225, 2, 89, // Opcode: CLASS_S
/* 709 */     MCD::OPC_FilterValue, 28, 8, 0, // Skip to: 721
/* 713 */     MCD::OPC_CheckPredicate, 33, 108, 4, // Skip to: 1849
/* 717 */     MCD::OPC_Decode, 187, 8, 88, // Opcode: MIN_S
/* 721 */     MCD::OPC_FilterValue, 29, 8, 0, // Skip to: 733
/* 725 */     MCD::OPC_CheckPredicate, 33, 96, 4, // Skip to: 1849
/* 729 */     MCD::OPC_Decode, 146, 8, 88, // Opcode: MAX_S
/* 733 */     MCD::OPC_FilterValue, 30, 8, 0, // Skip to: 745
/* 737 */     MCD::OPC_CheckPredicate, 33, 84, 4, // Skip to: 1849
/* 741 */     MCD::OPC_Decode, 173, 8, 88, // Opcode: MINA_S
/* 745 */     MCD::OPC_FilterValue, 31, 76, 4, // Skip to: 1849
/* 749 */     MCD::OPC_CheckPredicate, 33, 72, 4, // Skip to: 1849
/* 753 */     MCD::OPC_Decode, 132, 8, 88, // Opcode: MAXA_S
/* 757 */     MCD::OPC_FilterValue, 17, 156, 0, // Skip to: 917
/* 761 */     MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 764 */     MCD::OPC_FilterValue, 16, 9, 0, // Skip to: 777
/* 768 */     MCD::OPC_CheckPredicate, 33, 53, 4, // Skip to: 1849
/* 772 */     MCD::OPC_Decode, 157, 11, 227, 1, // Opcode: SEL_D
/* 777 */     MCD::OPC_FilterValue, 20, 9, 0, // Skip to: 790
/* 781 */     MCD::OPC_CheckPredicate, 33, 40, 4, // Skip to: 1849
/* 785 */     MCD::OPC_Decode, 151, 11, 228, 1, // Opcode: SELEQZ_D
/* 790 */     MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 803
/* 794 */     MCD::OPC_CheckPredicate, 33, 27, 4, // Skip to: 1849
/* 798 */     MCD::OPC_Decode, 155, 11, 228, 1, // Opcode: SELNEZ_D
/* 803 */     MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 816
/* 807 */     MCD::OPC_CheckPredicate, 33, 14, 4, // Skip to: 1849
/* 811 */     MCD::OPC_Decode, 235, 7, 229, 1, // Opcode: MADDF_D
/* 816 */     MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 829
/* 820 */     MCD::OPC_CheckPredicate, 33, 1, 4, // Skip to: 1849
/* 824 */     MCD::OPC_Decode, 252, 8, 229, 1, // Opcode: MSUBF_D
/* 829 */     MCD::OPC_FilterValue, 26, 14, 0, // Skip to: 847
/* 833 */     MCD::OPC_CheckPredicate, 33, 244, 3, // Skip to: 1849
/* 837 */     MCD::OPC_CheckField, 16, 5, 0, 238, 3, // Skip to: 1849
/* 843 */     MCD::OPC_Decode, 220, 10, 100, // Opcode: RINT_D
/* 847 */     MCD::OPC_FilterValue, 27, 14, 0, // Skip to: 865
/* 851 */     MCD::OPC_CheckPredicate, 33, 226, 3, // Skip to: 1849
/* 855 */     MCD::OPC_CheckField, 16, 5, 0, 220, 3, // Skip to: 1849
/* 861 */     MCD::OPC_Decode, 224, 2, 100, // Opcode: CLASS_D
/* 865 */     MCD::OPC_FilterValue, 28, 9, 0, // Skip to: 878
/* 869 */     MCD::OPC_CheckPredicate, 33, 208, 3, // Skip to: 1849
/* 873 */     MCD::OPC_Decode, 186, 8, 228, 1, // Opcode: MIN_D
/* 878 */     MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 891
/* 882 */     MCD::OPC_CheckPredicate, 33, 195, 3, // Skip to: 1849
/* 886 */     MCD::OPC_Decode, 145, 8, 228, 1, // Opcode: MAX_D
/* 891 */     MCD::OPC_FilterValue, 30, 9, 0, // Skip to: 904
/* 895 */     MCD::OPC_CheckPredicate, 33, 182, 3, // Skip to: 1849
/* 899 */     MCD::OPC_Decode, 172, 8, 228, 1, // Opcode: MINA_D
/* 904 */     MCD::OPC_FilterValue, 31, 173, 3, // Skip to: 1849
/* 908 */     MCD::OPC_CheckPredicate, 33, 169, 3, // Skip to: 1849
/* 912 */     MCD::OPC_Decode, 131, 8, 228, 1, // Opcode: MAXA_D
/* 917 */     MCD::OPC_FilterValue, 20, 211, 0, // Skip to: 1132
/* 921 */     MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 924 */     MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 937
/* 928 */     MCD::OPC_CheckPredicate, 33, 149, 3, // Skip to: 1849
/* 932 */     MCD::OPC_Decode, 149, 3, 230, 1, // Opcode: CMP_F_S
/* 937 */     MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 950
/* 941 */     MCD::OPC_CheckPredicate, 33, 136, 3, // Skip to: 1849
/* 945 */     MCD::OPC_Decode, 179, 3, 230, 1, // Opcode: CMP_UN_S
/* 950 */     MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 963
/* 954 */     MCD::OPC_CheckPredicate, 33, 123, 3, // Skip to: 1849
/* 958 */     MCD::OPC_Decode, 147, 3, 230, 1, // Opcode: CMP_EQ_S
/* 963 */     MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 976
/* 967 */     MCD::OPC_CheckPredicate, 33, 110, 3, // Skip to: 1849
/* 971 */     MCD::OPC_Decode, 173, 3, 230, 1, // Opcode: CMP_UEQ_S
/* 976 */     MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 989
/* 980 */     MCD::OPC_CheckPredicate, 33, 97, 3, // Skip to: 1849
/* 984 */     MCD::OPC_Decode, 155, 3, 230, 1, // Opcode: CMP_LT_S
/* 989 */     MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 1002
/* 993 */     MCD::OPC_CheckPredicate, 33, 84, 3, // Skip to: 1849
/* 997 */     MCD::OPC_Decode, 177, 3, 230, 1, // Opcode: CMP_ULT_S
/* 1002 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 1015
/* 1006 */    MCD::OPC_CheckPredicate, 33, 71, 3, // Skip to: 1849
/* 1010 */    MCD::OPC_Decode, 152, 3, 230, 1, // Opcode: CMP_LE_S
/* 1015 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 1028
/* 1019 */    MCD::OPC_CheckPredicate, 33, 58, 3, // Skip to: 1849
/* 1023 */    MCD::OPC_Decode, 175, 3, 230, 1, // Opcode: CMP_ULE_S
/* 1028 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 1041
/* 1032 */    MCD::OPC_CheckPredicate, 33, 45, 3, // Skip to: 1849
/* 1036 */    MCD::OPC_Decode, 157, 3, 230, 1, // Opcode: CMP_SAF_S
/* 1041 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 1054
/* 1045 */    MCD::OPC_CheckPredicate, 33, 32, 3, // Skip to: 1849
/* 1049 */    MCD::OPC_Decode, 171, 3, 230, 1, // Opcode: CMP_SUN_S
/* 1054 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 1067
/* 1058 */    MCD::OPC_CheckPredicate, 33, 19, 3, // Skip to: 1849
/* 1062 */    MCD::OPC_Decode, 159, 3, 230, 1, // Opcode: CMP_SEQ_S
/* 1067 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 1080
/* 1071 */    MCD::OPC_CheckPredicate, 33, 6, 3, // Skip to: 1849
/* 1075 */    MCD::OPC_Decode, 165, 3, 230, 1, // Opcode: CMP_SUEQ_S
/* 1080 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 1093
/* 1084 */    MCD::OPC_CheckPredicate, 33, 249, 2, // Skip to: 1849
/* 1088 */    MCD::OPC_Decode, 163, 3, 230, 1, // Opcode: CMP_SLT_S
/* 1093 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 1106
/* 1097 */    MCD::OPC_CheckPredicate, 33, 236, 2, // Skip to: 1849
/* 1101 */    MCD::OPC_Decode, 169, 3, 230, 1, // Opcode: CMP_SULT_S
/* 1106 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 1119
/* 1110 */    MCD::OPC_CheckPredicate, 33, 223, 2, // Skip to: 1849
/* 1114 */    MCD::OPC_Decode, 161, 3, 230, 1, // Opcode: CMP_SLE_S
/* 1119 */    MCD::OPC_FilterValue, 15, 214, 2, // Skip to: 1849
/* 1123 */    MCD::OPC_CheckPredicate, 33, 210, 2, // Skip to: 1849
/* 1127 */    MCD::OPC_Decode, 167, 3, 230, 1, // Opcode: CMP_SULE_S
/* 1132 */    MCD::OPC_FilterValue, 21, 201, 2, // Skip to: 1849
/* 1136 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 1139 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 1152
/* 1143 */    MCD::OPC_CheckPredicate, 33, 190, 2, // Skip to: 1849
/* 1147 */    MCD::OPC_Decode, 148, 3, 231, 1, // Opcode: CMP_F_D
/* 1152 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 1165
/* 1156 */    MCD::OPC_CheckPredicate, 33, 177, 2, // Skip to: 1849
/* 1160 */    MCD::OPC_Decode, 178, 3, 231, 1, // Opcode: CMP_UN_D
/* 1165 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 1178
/* 1169 */    MCD::OPC_CheckPredicate, 33, 164, 2, // Skip to: 1849
/* 1173 */    MCD::OPC_Decode, 145, 3, 231, 1, // Opcode: CMP_EQ_D
/* 1178 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 1191
/* 1182 */    MCD::OPC_CheckPredicate, 33, 151, 2, // Skip to: 1849
/* 1186 */    MCD::OPC_Decode, 172, 3, 231, 1, // Opcode: CMP_UEQ_D
/* 1191 */    MCD::OPC_FilterValue, 4, 9, 0, // Skip to: 1204
/* 1195 */    MCD::OPC_CheckPredicate, 33, 138, 2, // Skip to: 1849
/* 1199 */    MCD::OPC_Decode, 153, 3, 231, 1, // Opcode: CMP_LT_D
/* 1204 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 1217
/* 1208 */    MCD::OPC_CheckPredicate, 33, 125, 2, // Skip to: 1849
/* 1212 */    MCD::OPC_Decode, 176, 3, 231, 1, // Opcode: CMP_ULT_D
/* 1217 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 1230
/* 1221 */    MCD::OPC_CheckPredicate, 33, 112, 2, // Skip to: 1849
/* 1225 */    MCD::OPC_Decode, 150, 3, 231, 1, // Opcode: CMP_LE_D
/* 1230 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 1243
/* 1234 */    MCD::OPC_CheckPredicate, 33, 99, 2, // Skip to: 1849
/* 1238 */    MCD::OPC_Decode, 174, 3, 231, 1, // Opcode: CMP_ULE_D
/* 1243 */    MCD::OPC_FilterValue, 8, 9, 0, // Skip to: 1256
/* 1247 */    MCD::OPC_CheckPredicate, 33, 86, 2, // Skip to: 1849
/* 1251 */    MCD::OPC_Decode, 156, 3, 231, 1, // Opcode: CMP_SAF_D
/* 1256 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 1269
/* 1260 */    MCD::OPC_CheckPredicate, 33, 73, 2, // Skip to: 1849
/* 1264 */    MCD::OPC_Decode, 170, 3, 231, 1, // Opcode: CMP_SUN_D
/* 1269 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 1282
/* 1273 */    MCD::OPC_CheckPredicate, 33, 60, 2, // Skip to: 1849
/* 1277 */    MCD::OPC_Decode, 158, 3, 231, 1, // Opcode: CMP_SEQ_D
/* 1282 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 1295
/* 1286 */    MCD::OPC_CheckPredicate, 33, 47, 2, // Skip to: 1849
/* 1290 */    MCD::OPC_Decode, 164, 3, 231, 1, // Opcode: CMP_SUEQ_D
/* 1295 */    MCD::OPC_FilterValue, 12, 9, 0, // Skip to: 1308
/* 1299 */    MCD::OPC_CheckPredicate, 33, 34, 2, // Skip to: 1849
/* 1303 */    MCD::OPC_Decode, 162, 3, 231, 1, // Opcode: CMP_SLT_D
/* 1308 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 1321
/* 1312 */    MCD::OPC_CheckPredicate, 33, 21, 2, // Skip to: 1849
/* 1316 */    MCD::OPC_Decode, 168, 3, 231, 1, // Opcode: CMP_SULT_D
/* 1321 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 1334
/* 1325 */    MCD::OPC_CheckPredicate, 33, 8, 2, // Skip to: 1849
/* 1329 */    MCD::OPC_Decode, 160, 3, 231, 1, // Opcode: CMP_SLE_D
/* 1334 */    MCD::OPC_FilterValue, 15, 255, 1, // Skip to: 1849
/* 1338 */    MCD::OPC_CheckPredicate, 33, 251, 1, // Skip to: 1849
/* 1342 */    MCD::OPC_Decode, 166, 3, 231, 1, // Opcode: CMP_SULE_D
/* 1347 */    MCD::OPC_FilterValue, 18, 81, 0, // Skip to: 1432
/* 1351 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 1354 */    MCD::OPC_FilterValue, 9, 9, 0, // Skip to: 1367
/* 1358 */    MCD::OPC_CheckPredicate, 33, 231, 1, // Skip to: 1849
/* 1362 */    MCD::OPC_Decode, 178, 1, 232, 1, // Opcode: BC2EQZ
/* 1367 */    MCD::OPC_FilterValue, 10, 9, 0, // Skip to: 1380
/* 1371 */    MCD::OPC_CheckPredicate, 33, 218, 1, // Skip to: 1849
/* 1375 */    MCD::OPC_Decode, 197, 7, 233, 1, // Opcode: LWC2_R6
/* 1380 */    MCD::OPC_FilterValue, 11, 9, 0, // Skip to: 1393
/* 1384 */    MCD::OPC_CheckPredicate, 33, 205, 1, // Skip to: 1849
/* 1388 */    MCD::OPC_Decode, 216, 12, 233, 1, // Opcode: SWC2_R6
/* 1393 */    MCD::OPC_FilterValue, 13, 9, 0, // Skip to: 1406
/* 1397 */    MCD::OPC_CheckPredicate, 33, 192, 1, // Skip to: 1849
/* 1401 */    MCD::OPC_Decode, 179, 1, 232, 1, // Opcode: BC2NEZ
/* 1406 */    MCD::OPC_FilterValue, 14, 9, 0, // Skip to: 1419
/* 1410 */    MCD::OPC_CheckPredicate, 33, 179, 1, // Skip to: 1849
/* 1414 */    MCD::OPC_Decode, 144, 7, 233, 1, // Opcode: LDC2_R6
/* 1419 */    MCD::OPC_FilterValue, 15, 170, 1, // Skip to: 1849
/* 1423 */    MCD::OPC_CheckPredicate, 33, 166, 1, // Skip to: 1849
/* 1427 */    MCD::OPC_Decode, 135, 11, 233, 1, // Opcode: SDC2_R6
/* 1432 */    MCD::OPC_FilterValue, 22, 9, 0, // Skip to: 1445
/* 1436 */    MCD::OPC_CheckPredicate, 33, 153, 1, // Skip to: 1849
/* 1440 */    MCD::OPC_Decode, 206, 1, 234, 1, // Opcode: BGEZC
/* 1445 */    MCD::OPC_FilterValue, 23, 9, 0, // Skip to: 1458
/* 1449 */    MCD::OPC_CheckPredicate, 33, 140, 1, // Skip to: 1849
/* 1453 */    MCD::OPC_Decode, 248, 1, 235, 1, // Opcode: BLTZC
/* 1458 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 1471
/* 1462 */    MCD::OPC_CheckPredicate, 33, 127, 1, // Skip to: 1849
/* 1466 */    MCD::OPC_Decode, 129, 2, 236, 1, // Opcode: BNEC
/* 1471 */    MCD::OPC_FilterValue, 29, 9, 0, // Skip to: 1484
/* 1475 */    MCD::OPC_CheckPredicate, 34, 114, 1, // Skip to: 1849
/* 1479 */    MCD::OPC_Decode, 147, 4, 237, 1, // Opcode: DAUI
/* 1484 */    MCD::OPC_FilterValue, 31, 182, 0, // Skip to: 1670
/* 1488 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 1491 */    MCD::OPC_FilterValue, 32, 40, 0, // Skip to: 1535
/* 1495 */    MCD::OPC_ExtractField, 8, 3,  // Inst{10-8} ...
/* 1498 */    MCD::OPC_FilterValue, 0, 21, 0, // Skip to: 1523
/* 1502 */    MCD::OPC_CheckPredicate, 33, 87, 1, // Skip to: 1849
/* 1506 */    MCD::OPC_CheckField, 21, 5, 0, 81, 1, // Skip to: 1849
/* 1512 */    MCD::OPC_CheckField, 6, 2, 0, 75, 1, // Skip to: 1849
/* 1518 */    MCD::OPC_Decode, 232, 1, 200, 1, // Opcode: BITSWAP
/* 1523 */    MCD::OPC_FilterValue, 2, 66, 1, // Skip to: 1849
/* 1527 */    MCD::OPC_CheckPredicate, 33, 62, 1, // Skip to: 1849
/* 1531 */    MCD::OPC_Decode, 80, 216, 1, // Opcode: ALIGN
/* 1535 */    MCD::OPC_FilterValue, 36, 41, 0, // Skip to: 1580
/* 1539 */    MCD::OPC_ExtractField, 9, 2,  // Inst{10-9} ...
/* 1542 */    MCD::OPC_FilterValue, 0, 21, 0, // Skip to: 1567
/* 1546 */    MCD::OPC_CheckPredicate, 34, 43, 1, // Skip to: 1849
/* 1550 */    MCD::OPC_CheckField, 21, 5, 0, 37, 1, // Skip to: 1849
/* 1556 */    MCD::OPC_CheckField, 6, 3, 0, 31, 1, // Skip to: 1849
/* 1562 */    MCD::OPC_Decode, 148, 4, 238, 1, // Opcode: DBITSWAP
/* 1567 */    MCD::OPC_FilterValue, 1, 22, 1, // Skip to: 1849
/* 1571 */    MCD::OPC_CheckPredicate, 34, 18, 1, // Skip to: 1849
/* 1575 */    MCD::OPC_Decode, 145, 4, 239, 1, // Opcode: DALIGN
/* 1580 */    MCD::OPC_FilterValue, 37, 15, 0, // Skip to: 1599
/* 1584 */    MCD::OPC_CheckPredicate, 33, 5, 1, // Skip to: 1849
/* 1588 */    MCD::OPC_CheckField, 6, 1, 0, 255, 0, // Skip to: 1849
/* 1594 */    MCD::OPC_Decode, 203, 2, 240, 1, // Opcode: CACHE_R6
/* 1599 */    MCD::OPC_FilterValue, 38, 9, 0, // Skip to: 1612
/* 1603 */    MCD::OPC_CheckPredicate, 33, 242, 0, // Skip to: 1849
/* 1607 */    MCD::OPC_Decode, 253, 10, 241, 1, // Opcode: SC_R6
/* 1612 */    MCD::OPC_FilterValue, 39, 9, 0, // Skip to: 1625
/* 1616 */    MCD::OPC_CheckPredicate, 33, 229, 0, // Skip to: 1849
/* 1620 */    MCD::OPC_Decode, 251, 10, 241, 1, // Opcode: SCD_R6
/* 1625 */    MCD::OPC_FilterValue, 53, 15, 0, // Skip to: 1644
/* 1629 */    MCD::OPC_CheckPredicate, 33, 216, 0, // Skip to: 1849
/* 1633 */    MCD::OPC_CheckField, 6, 1, 0, 210, 0, // Skip to: 1849
/* 1639 */    MCD::OPC_Decode, 158, 10, 240, 1, // Opcode: PREF_R6
/* 1644 */    MCD::OPC_FilterValue, 54, 9, 0, // Skip to: 1657
/* 1648 */    MCD::OPC_CheckPredicate, 33, 197, 0, // Skip to: 1849
/* 1652 */    MCD::OPC_Decode, 175, 7, 241, 1, // Opcode: LL_R6
/* 1657 */    MCD::OPC_FilterValue, 55, 188, 0, // Skip to: 1849
/* 1661 */    MCD::OPC_CheckPredicate, 33, 184, 0, // Skip to: 1849
/* 1665 */    MCD::OPC_Decode, 173, 7, 241, 1, // Opcode: LLD_R6
/* 1670 */    MCD::OPC_FilterValue, 50, 9, 0, // Skip to: 1683
/* 1674 */    MCD::OPC_CheckPredicate, 33, 171, 0, // Skip to: 1849
/* 1678 */    MCD::OPC_Decode, 169, 1, 242, 1, // Opcode: BC
/* 1683 */    MCD::OPC_FilterValue, 54, 24, 0, // Skip to: 1711
/* 1687 */    MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 1702
/* 1691 */    MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 1702
/* 1697 */    MCD::OPC_Decode, 243, 6, 243, 1, // Opcode: JIC
/* 1702 */    MCD::OPC_CheckPredicate, 33, 143, 0, // Skip to: 1849
/* 1706 */    MCD::OPC_Decode, 194, 1, 244, 1, // Opcode: BEQZC
/* 1711 */    MCD::OPC_FilterValue, 58, 9, 0, // Skip to: 1724
/* 1715 */    MCD::OPC_CheckPredicate, 33, 130, 0, // Skip to: 1849
/* 1719 */    MCD::OPC_Decode, 166, 1, 242, 1, // Opcode: BALC
/* 1724 */    MCD::OPC_FilterValue, 59, 93, 0, // Skip to: 1821
/* 1728 */    MCD::OPC_ExtractField, 19, 2,  // Inst{20-19} ...
/* 1731 */    MCD::OPC_FilterValue, 0, 8, 0, // Skip to: 1743
/* 1735 */    MCD::OPC_CheckPredicate, 33, 110, 0, // Skip to: 1849
/* 1739 */    MCD::OPC_Decode, 26, 245, 1, // Opcode: ADDIUPC
/* 1743 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 1756
/* 1747 */    MCD::OPC_CheckPredicate, 33, 98, 0, // Skip to: 1849
/* 1751 */    MCD::OPC_Decode, 204, 7, 245, 1, // Opcode: LWPC
/* 1756 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 1769
/* 1760 */    MCD::OPC_CheckPredicate, 33, 85, 0, // Skip to: 1849
/* 1764 */    MCD::OPC_Decode, 210, 7, 245, 1, // Opcode: LWUPC
/* 1769 */    MCD::OPC_FilterValue, 3, 76, 0, // Skip to: 1849
/* 1773 */    MCD::OPC_ExtractField, 18, 1,  // Inst{18} ...
/* 1776 */    MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 1789
/* 1780 */    MCD::OPC_CheckPredicate, 34, 65, 0, // Skip to: 1849
/* 1784 */    MCD::OPC_Decode, 151, 7, 246, 1, // Opcode: LDPC
/* 1789 */    MCD::OPC_FilterValue, 1, 56, 0, // Skip to: 1849
/* 1793 */    MCD::OPC_ExtractField, 16, 2,  // Inst{17-16} ...
/* 1796 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 1809
/* 1800 */    MCD::OPC_CheckPredicate, 33, 45, 0, // Skip to: 1849
/* 1804 */    MCD::OPC_Decode, 137, 1, 247, 1, // Opcode: AUIPC
/* 1809 */    MCD::OPC_FilterValue, 3, 36, 0, // Skip to: 1849
/* 1813 */    MCD::OPC_CheckPredicate, 33, 32, 0, // Skip to: 1849
/* 1817 */    MCD::OPC_Decode, 81, 247, 1, // Opcode: ALUIPC
/* 1821 */    MCD::OPC_FilterValue, 62, 24, 0, // Skip to: 1849
/* 1825 */    MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 1840
/* 1829 */    MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 1840
/* 1835 */    MCD::OPC_Decode, 242, 6, 243, 1, // Opcode: JIALC
/* 1840 */    MCD::OPC_CheckPredicate, 33, 5, 0, // Skip to: 1849
/* 1844 */    MCD::OPC_Decode, 141, 2, 244, 1, // Opcode: BNEZC
/* 1849 */    MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMips32r6_64r6_Ambiguous32[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 6, 24, 0, // Skip to: 31
/* 7 */       MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 22
/* 11 */      MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 22
/* 17 */      MCD::OPC_Decode, 235, 1, 221, 1, // Opcode: BLEZALC
/* 22 */      MCD::OPC_CheckPredicate, 33, 145, 0, // Skip to: 171
/* 26 */      MCD::OPC_Decode, 198, 1, 221, 1, // Opcode: BGEUC
/* 31 */      MCD::OPC_FilterValue, 7, 24, 0, // Skip to: 59
/* 35 */      MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 50
/* 39 */      MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 50
/* 45 */      MCD::OPC_Decode, 211, 1, 222, 1, // Opcode: BGTZALC
/* 50 */      MCD::OPC_CheckPredicate, 33, 117, 0, // Skip to: 171
/* 54 */      MCD::OPC_Decode, 240, 1, 222, 1, // Opcode: BLTUC
/* 59 */      MCD::OPC_FilterValue, 8, 24, 0, // Skip to: 87
/* 63 */      MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 78
/* 67 */      MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 78
/* 73 */      MCD::OPC_Decode, 193, 1, 236, 1, // Opcode: BEQZALC
/* 78 */      MCD::OPC_CheckPredicate, 33, 89, 0, // Skip to: 171
/* 82 */      MCD::OPC_Decode, 150, 2, 223, 1, // Opcode: BOVC
/* 87 */      MCD::OPC_FilterValue, 22, 24, 0, // Skip to: 115
/* 91 */      MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 106
/* 95 */      MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 106
/* 101 */     MCD::OPC_Decode, 236, 1, 234, 1, // Opcode: BLEZC
/* 106 */     MCD::OPC_CheckPredicate, 33, 61, 0, // Skip to: 171
/* 110 */     MCD::OPC_Decode, 197, 1, 234, 1, // Opcode: BGEC
/* 115 */     MCD::OPC_FilterValue, 23, 24, 0, // Skip to: 143
/* 119 */     MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 134
/* 123 */     MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 134
/* 129 */     MCD::OPC_Decode, 212, 1, 235, 1, // Opcode: BGTZC
/* 134 */     MCD::OPC_CheckPredicate, 33, 33, 0, // Skip to: 171
/* 138 */     MCD::OPC_Decode, 239, 1, 235, 1, // Opcode: BLTC
/* 143 */     MCD::OPC_FilterValue, 24, 24, 0, // Skip to: 171
/* 147 */     MCD::OPC_CheckPredicate, 33, 11, 0, // Skip to: 162
/* 151 */     MCD::OPC_CheckField, 21, 5, 0, 5, 0, // Skip to: 162
/* 157 */     MCD::OPC_Decode, 140, 2, 236, 1, // Opcode: BNEZALC
/* 162 */     MCD::OPC_CheckPredicate, 33, 5, 0, // Skip to: 171
/* 166 */     MCD::OPC_Decode, 144, 2, 236, 1, // Opcode: BNVC
/* 171 */     MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMips32r6_64r6_GP6432[] = {
/* 0 */       MCD::OPC_ExtractField, 0, 11,  // Inst{10-0} ...
/* 3 */       MCD::OPC_FilterValue, 53, 15, 0, // Skip to: 22
/* 7 */       MCD::OPC_CheckPredicate, 36, 30, 0, // Skip to: 41
/* 11 */      MCD::OPC_CheckField, 26, 6, 0, 24, 0, // Skip to: 41
/* 17 */      MCD::OPC_Decode, 150, 11, 219, 1, // Opcode: SELEQZ64
/* 22 */      MCD::OPC_FilterValue, 55, 15, 0, // Skip to: 41
/* 26 */      MCD::OPC_CheckPredicate, 36, 11, 0, // Skip to: 41
/* 30 */      MCD::OPC_CheckField, 26, 6, 0, 5, 0, // Skip to: 41
/* 36 */      MCD::OPC_Decode, 154, 11, 219, 1, // Opcode: SELNEZ64
/* 41 */      MCD::OPC_Fail,
  0
};

static const uint8_t DecoderTableMips6432[] = {
/* 0 */       MCD::OPC_ExtractField, 26, 6,  // Inst{31-26} ...
/* 3 */       MCD::OPC_FilterValue, 0, 112, 1, // Skip to: 375
/* 7 */       MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 10 */      MCD::OPC_FilterValue, 20, 15, 0, // Skip to: 29
/* 14 */      MCD::OPC_CheckPredicate, 17, 194, 8, // Skip to: 2260
/* 18 */      MCD::OPC_CheckField, 6, 5, 0, 188, 8, // Skip to: 2260
/* 24 */      MCD::OPC_Decode, 236, 4, 248, 1, // Opcode: DSLLV
/* 29 */      MCD::OPC_FilterValue, 22, 29, 0, // Skip to: 62
/* 33 */      MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 36 */      MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 49
/* 40 */      MCD::OPC_CheckPredicate, 17, 168, 8, // Skip to: 2260
/* 44 */      MCD::OPC_Decode, 242, 4, 248, 1, // Opcode: DSRLV
/* 49 */      MCD::OPC_FilterValue, 1, 159, 8, // Skip to: 2260
/* 53 */      MCD::OPC_CheckPredicate, 37, 155, 8, // Skip to: 2260
/* 57 */      MCD::OPC_Decode, 229, 4, 248, 1, // Opcode: DROTRV
/* 62 */      MCD::OPC_FilterValue, 23, 15, 0, // Skip to: 81
/* 66 */      MCD::OPC_CheckPredicate, 17, 142, 8, // Skip to: 2260
/* 70 */      MCD::OPC_CheckField, 6, 5, 0, 136, 8, // Skip to: 2260
/* 76 */      MCD::OPC_Decode, 239, 4, 248, 1, // Opcode: DSRAV
/* 81 */      MCD::OPC_FilterValue, 28, 15, 0, // Skip to: 100
/* 85 */      MCD::OPC_CheckPredicate, 38, 123, 8, // Skip to: 2260
/* 89 */      MCD::OPC_CheckField, 6, 10, 0, 117, 8, // Skip to: 2260
/* 95 */      MCD::OPC_Decode, 188, 4, 249, 1, // Opcode: DMULT
/* 100 */     MCD::OPC_FilterValue, 29, 15, 0, // Skip to: 119
/* 104 */     MCD::OPC_CheckPredicate, 38, 104, 8, // Skip to: 2260
/* 108 */     MCD::OPC_CheckField, 6, 10, 0, 98, 8, // Skip to: 2260
/* 114 */     MCD::OPC_Decode, 189, 4, 249, 1, // Opcode: DMULTu
/* 119 */     MCD::OPC_FilterValue, 30, 15, 0, // Skip to: 138
/* 123 */     MCD::OPC_CheckPredicate, 38, 85, 8, // Skip to: 2260
/* 127 */     MCD::OPC_CheckField, 6, 10, 0, 79, 8, // Skip to: 2260
/* 133 */     MCD::OPC_Decode, 231, 4, 249, 1, // Opcode: DSDIV
/* 138 */     MCD::OPC_FilterValue, 31, 15, 0, // Skip to: 157
/* 142 */     MCD::OPC_CheckPredicate, 38, 66, 8, // Skip to: 2260
/* 146 */     MCD::OPC_CheckField, 6, 10, 0, 60, 8, // Skip to: 2260
/* 152 */     MCD::OPC_Decode, 245, 4, 249, 1, // Opcode: DUDIV
/* 157 */     MCD::OPC_FilterValue, 44, 15, 0, // Skip to: 176
/* 161 */     MCD::OPC_CheckPredicate, 17, 47, 8, // Skip to: 2260
/* 165 */     MCD::OPC_CheckField, 6, 5, 0, 41, 8, // Skip to: 2260
/* 171 */     MCD::OPC_Decode, 140, 4, 219, 1, // Opcode: DADD
/* 176 */     MCD::OPC_FilterValue, 45, 15, 0, // Skip to: 195
/* 180 */     MCD::OPC_CheckPredicate, 17, 28, 8, // Skip to: 2260
/* 184 */     MCD::OPC_CheckField, 6, 5, 0, 22, 8, // Skip to: 2260
/* 190 */     MCD::OPC_Decode, 143, 4, 219, 1, // Opcode: DADDu
/* 195 */     MCD::OPC_FilterValue, 46, 15, 0, // Skip to: 214
/* 199 */     MCD::OPC_CheckPredicate, 17, 9, 8, // Skip to: 2260
/* 203 */     MCD::OPC_CheckField, 6, 5, 0, 3, 8, // Skip to: 2260
/* 209 */     MCD::OPC_Decode, 243, 4, 219, 1, // Opcode: DSUB
/* 214 */     MCD::OPC_FilterValue, 47, 15, 0, // Skip to: 233
/* 218 */     MCD::OPC_CheckPredicate, 17, 246, 7, // Skip to: 2260
/* 222 */     MCD::OPC_CheckField, 6, 5, 0, 240, 7, // Skip to: 2260
/* 228 */     MCD::OPC_Decode, 244, 4, 219, 1, // Opcode: DSUBu
/* 233 */     MCD::OPC_FilterValue, 56, 15, 0, // Skip to: 252
/* 237 */     MCD::OPC_CheckPredicate, 17, 227, 7, // Skip to: 2260
/* 241 */     MCD::OPC_CheckField, 21, 5, 0, 221, 7, // Skip to: 2260
/* 247 */     MCD::OPC_Decode, 233, 4, 250, 1, // Opcode: DSLL
/* 252 */     MCD::OPC_FilterValue, 58, 29, 0, // Skip to: 285
/* 256 */     MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 259 */     MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 272
/* 263 */     MCD::OPC_CheckPredicate, 17, 201, 7, // Skip to: 2260
/* 267 */     MCD::OPC_Decode, 240, 4, 250, 1, // Opcode: DSRL
/* 272 */     MCD::OPC_FilterValue, 1, 192, 7, // Skip to: 2260
/* 276 */     MCD::OPC_CheckPredicate, 37, 188, 7, // Skip to: 2260
/* 280 */     MCD::OPC_Decode, 227, 4, 250, 1, // Opcode: DROTR
/* 285 */     MCD::OPC_FilterValue, 59, 15, 0, // Skip to: 304
/* 289 */     MCD::OPC_CheckPredicate, 17, 175, 7, // Skip to: 2260
/* 293 */     MCD::OPC_CheckField, 21, 5, 0, 169, 7, // Skip to: 2260
/* 299 */     MCD::OPC_Decode, 237, 4, 250, 1, // Opcode: DSRA
/* 304 */     MCD::OPC_FilterValue, 60, 15, 0, // Skip to: 323
/* 308 */     MCD::OPC_CheckPredicate, 17, 156, 7, // Skip to: 2260
/* 312 */     MCD::OPC_CheckField, 21, 5, 0, 150, 7, // Skip to: 2260
/* 318 */     MCD::OPC_Decode, 234, 4, 250, 1, // Opcode: DSLL32
/* 323 */     MCD::OPC_FilterValue, 62, 29, 0, // Skip to: 356
/* 327 */     MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 330 */     MCD::OPC_FilterValue, 0, 9, 0, // Skip to: 343
/* 334 */     MCD::OPC_CheckPredicate, 17, 130, 7, // Skip to: 2260
/* 338 */     MCD::OPC_Decode, 241, 4, 250, 1, // Opcode: DSRL32
/* 343 */     MCD::OPC_FilterValue, 1, 121, 7, // Skip to: 2260
/* 347 */     MCD::OPC_CheckPredicate, 37, 117, 7, // Skip to: 2260
/* 351 */     MCD::OPC_Decode, 228, 4, 250, 1, // Opcode: DROTR32
/* 356 */     MCD::OPC_FilterValue, 63, 108, 7, // Skip to: 2260
/* 360 */     MCD::OPC_CheckPredicate, 17, 104, 7, // Skip to: 2260
/* 364 */     MCD::OPC_CheckField, 21, 5, 0, 98, 7, // Skip to: 2260
/* 370 */     MCD::OPC_Decode, 238, 4, 250, 1, // Opcode: DSRA32
/* 375 */     MCD::OPC_FilterValue, 16, 41, 0, // Skip to: 420
/* 379 */     MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 382 */     MCD::OPC_FilterValue, 1, 15, 0, // Skip to: 401
/* 386 */     MCD::OPC_CheckPredicate, 39, 78, 7, // Skip to: 2260
/* 390 */     MCD::OPC_CheckField, 3, 8, 0, 72, 7, // Skip to: 2260
/* 396 */     MCD::OPC_Decode, 177, 4, 251, 1, // Opcode: DMFC0
/* 401 */     MCD::OPC_FilterValue, 5, 63, 7, // Skip to: 2260
/* 405 */     MCD::OPC_CheckPredicate, 39, 59, 7, // Skip to: 2260
/* 409 */     MCD::OPC_CheckField, 3, 8, 0, 53, 7, // Skip to: 2260
/* 415 */     MCD::OPC_Decode, 182, 4, 251, 1, // Opcode: DMTC0
/* 420 */     MCD::OPC_FilterValue, 17, 222, 3, // Skip to: 1414
/* 424 */     MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 427 */     MCD::OPC_FilterValue, 0, 54, 0, // Skip to: 485
/* 431 */     MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 434 */     MCD::OPC_FilterValue, 3, 15, 0, // Skip to: 453
/* 438 */     MCD::OPC_CheckPredicate, 40, 26, 7, // Skip to: 2260
/* 442 */     MCD::OPC_CheckField, 6, 5, 0, 20, 7, // Skip to: 2260
/* 448 */     MCD::OPC_Decode, 160, 8, 252, 1, // Opcode: MFHC1_D64
/* 453 */     MCD::OPC_FilterValue, 7, 15, 0, // Skip to: 472
/* 457 */     MCD::OPC_CheckPredicate, 40, 7, 7, // Skip to: 2260
/* 461 */     MCD::OPC_CheckField, 6, 5, 0, 1, 7, // Skip to: 2260
/* 467 */     MCD::OPC_Decode, 149, 9, 253, 1, // Opcode: MTHC1_D64
/* 472 */     MCD::OPC_FilterValue, 17, 248, 6, // Skip to: 2260
/* 476 */     MCD::OPC_CheckPredicate, 41, 244, 6, // Skip to: 2260
/* 480 */     MCD::OPC_Decode, 153, 5, 228, 1, // Opcode: FADD_D64
/* 485 */     MCD::OPC_FilterValue, 1, 15, 0, // Skip to: 504
/* 489 */     MCD::OPC_CheckPredicate, 41, 231, 6, // Skip to: 2260
/* 493 */     MCD::OPC_CheckField, 21, 5, 17, 225, 6, // Skip to: 2260
/* 499 */     MCD::OPC_Decode, 155, 6, 228, 1, // Opcode: FSUB_D64
/* 504 */     MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 523
/* 508 */     MCD::OPC_CheckPredicate, 41, 212, 6, // Skip to: 2260
/* 512 */     MCD::OPC_CheckField, 21, 5, 17, 206, 6, // Skip to: 2260
/* 518 */     MCD::OPC_Decode, 246, 5, 228, 1, // Opcode: FMUL_D64
/* 523 */     MCD::OPC_FilterValue, 3, 15, 0, // Skip to: 542
/* 527 */     MCD::OPC_CheckPredicate, 41, 193, 6, // Skip to: 2260
/* 531 */     MCD::OPC_CheckField, 21, 5, 17, 187, 6, // Skip to: 2260
/* 537 */     MCD::OPC_Decode, 189, 5, 228, 1, // Opcode: FDIV_D64
/* 542 */     MCD::OPC_FilterValue, 4, 15, 0, // Skip to: 561
/* 546 */     MCD::OPC_CheckPredicate, 42, 174, 6, // Skip to: 2260
/* 550 */     MCD::OPC_CheckField, 16, 10, 160, 4, 167, 6, // Skip to: 2260
/* 557 */     MCD::OPC_Decode, 148, 6, 100, // Opcode: FSQRT_D64
/* 561 */     MCD::OPC_FilterValue, 5, 15, 0, // Skip to: 580
/* 565 */     MCD::OPC_CheckPredicate, 41, 155, 6, // Skip to: 2260
/* 569 */     MCD::OPC_CheckField, 16, 10, 160, 4, 148, 6, // Skip to: 2260
/* 576 */     MCD::OPC_Decode, 146, 5, 100, // Opcode: FABS_D64
/* 580 */     MCD::OPC_FilterValue, 6, 15, 0, // Skip to: 599
/* 584 */     MCD::OPC_CheckPredicate, 41, 136, 6, // Skip to: 2260
/* 588 */     MCD::OPC_CheckField, 16, 10, 160, 4, 129, 6, // Skip to: 2260
/* 595 */     MCD::OPC_Decode, 239, 5, 100, // Opcode: FMOV_D64
/* 599 */     MCD::OPC_FilterValue, 7, 15, 0, // Skip to: 618
/* 603 */     MCD::OPC_CheckPredicate, 41, 117, 6, // Skip to: 2260
/* 607 */     MCD::OPC_CheckField, 16, 10, 160, 4, 110, 6, // Skip to: 2260
/* 614 */     MCD::OPC_Decode, 252, 5, 100, // Opcode: FNEG_D64
/* 618 */     MCD::OPC_FilterValue, 8, 29, 0, // Skip to: 651
/* 622 */     MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 625 */     MCD::OPC_FilterValue, 128, 4, 8, 0, // Skip to: 638
/* 630 */     MCD::OPC_CheckPredicate, 41, 90, 6, // Skip to: 2260
/* 634 */     MCD::OPC_Decode, 227, 10, 93, // Opcode: ROUND_L_S
/* 638 */     MCD::OPC_FilterValue, 160, 4, 81, 6, // Skip to: 2260
/* 643 */     MCD::OPC_CheckPredicate, 41, 77, 6, // Skip to: 2260
/* 647 */     MCD::OPC_Decode, 226, 10, 100, // Opcode: ROUND_L_D64
/* 651 */     MCD::OPC_FilterValue, 9, 29, 0, // Skip to: 684
/* 655 */     MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 658 */     MCD::OPC_FilterValue, 128, 4, 8, 0, // Skip to: 671
/* 663 */     MCD::OPC_CheckPredicate, 41, 57, 6, // Skip to: 2260
/* 667 */     MCD::OPC_Decode, 189, 13, 93, // Opcode: TRUNC_L_S
/* 671 */     MCD::OPC_FilterValue, 160, 4, 48, 6, // Skip to: 2260
/* 676 */     MCD::OPC_CheckPredicate, 41, 44, 6, // Skip to: 2260
/* 680 */     MCD::OPC_Decode, 188, 13, 100, // Opcode: TRUNC_L_D64
/* 684 */     MCD::OPC_FilterValue, 10, 29, 0, // Skip to: 717
/* 688 */     MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 691 */     MCD::OPC_FilterValue, 128, 4, 8, 0, // Skip to: 704
/* 696 */     MCD::OPC_CheckPredicate, 41, 24, 6, // Skip to: 2260
/* 700 */     MCD::OPC_Decode, 205, 2, 93, // Opcode: CEIL_L_S
/* 704 */     MCD::OPC_FilterValue, 160, 4, 15, 6, // Skip to: 2260
/* 709 */     MCD::OPC_CheckPredicate, 41, 11, 6, // Skip to: 2260
/* 713 */     MCD::OPC_Decode, 204, 2, 100, // Opcode: CEIL_L_D64
/* 717 */     MCD::OPC_FilterValue, 11, 29, 0, // Skip to: 750
/* 721 */     MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 724 */     MCD::OPC_FilterValue, 128, 4, 8, 0, // Skip to: 737
/* 729 */     MCD::OPC_CheckPredicate, 41, 247, 5, // Skip to: 2260
/* 733 */     MCD::OPC_Decode, 221, 5, 93, // Opcode: FLOOR_L_S
/* 737 */     MCD::OPC_FilterValue, 160, 4, 238, 5, // Skip to: 2260
/* 742 */     MCD::OPC_CheckPredicate, 41, 234, 5, // Skip to: 2260
/* 746 */     MCD::OPC_Decode, 220, 5, 100, // Opcode: FLOOR_L_D64
/* 750 */     MCD::OPC_FilterValue, 12, 16, 0, // Skip to: 770
/* 754 */     MCD::OPC_CheckPredicate, 42, 222, 5, // Skip to: 2260
/* 758 */     MCD::OPC_CheckField, 16, 10, 160, 4, 215, 5, // Skip to: 2260
/* 765 */     MCD::OPC_Decode, 229, 10, 254, 1, // Opcode: ROUND_W_D64
/* 770 */     MCD::OPC_FilterValue, 13, 16, 0, // Skip to: 790
/* 774 */     MCD::OPC_CheckPredicate, 42, 202, 5, // Skip to: 2260
/* 778 */     MCD::OPC_CheckField, 16, 10, 160, 4, 195, 5, // Skip to: 2260
/* 785 */     MCD::OPC_Decode, 191, 13, 254, 1, // Opcode: TRUNC_W_D64
/* 790 */     MCD::OPC_FilterValue, 14, 16, 0, // Skip to: 810
/* 794 */     MCD::OPC_CheckPredicate, 42, 182, 5, // Skip to: 2260
/* 798 */     MCD::OPC_CheckField, 16, 10, 160, 4, 175, 5, // Skip to: 2260
/* 805 */     MCD::OPC_Decode, 207, 2, 254, 1, // Opcode: CEIL_W_D64
/* 810 */     MCD::OPC_FilterValue, 15, 16, 0, // Skip to: 830
/* 814 */     MCD::OPC_CheckPredicate, 42, 162, 5, // Skip to: 2260
/* 818 */     MCD::OPC_CheckField, 16, 10, 160, 4, 155, 5, // Skip to: 2260
/* 825 */     MCD::OPC_Decode, 223, 5, 254, 1, // Opcode: FLOOR_W_D64
/* 830 */     MCD::OPC_FilterValue, 17, 41, 0, // Skip to: 875
/* 834 */     MCD::OPC_ExtractField, 16, 2,  // Inst{17-16} ...
/* 837 */     MCD::OPC_FilterValue, 0, 15, 0, // Skip to: 856
/* 841 */     MCD::OPC_CheckPredicate, 43, 135, 5, // Skip to: 2260
/* 845 */     MCD::OPC_CheckField, 21, 5, 17, 129, 5, // Skip to: 2260
/* 851 */     MCD::OPC_Decode, 213, 8, 255, 1, // Opcode: MOVF_D64
/* 856 */     MCD::OPC_FilterValue, 1, 120, 5, // Skip to: 2260
/* 860 */     MCD::OPC_CheckPredicate, 43, 116, 5, // Skip to: 2260
/* 864 */     MCD::OPC_CheckField, 21, 5, 17, 110, 5, // Skip to: 2260
/* 870 */     MCD::OPC_Decode, 233, 8, 255, 1, // Opcode: MOVT_D64
/* 875 */     MCD::OPC_FilterValue, 18, 15, 0, // Skip to: 894
/* 879 */     MCD::OPC_CheckPredicate, 43, 97, 5, // Skip to: 2260
/* 883 */     MCD::OPC_CheckField, 21, 5, 17, 91, 5, // Skip to: 2260
/* 889 */     MCD::OPC_Decode, 245, 8, 128, 2, // Opcode: MOVZ_I_D64
/* 894 */     MCD::OPC_FilterValue, 19, 15, 0, // Skip to: 913
/* 898 */     MCD::OPC_CheckPredicate, 43, 78, 5, // Skip to: 2260
/* 902 */     MCD::OPC_CheckField, 21, 5, 17, 72, 5, // Skip to: 2260
/* 908 */     MCD::OPC_Decode, 225, 8, 128, 2, // Opcode: MOVN_I_D64
/* 913 */     MCD::OPC_FilterValue, 32, 31, 0, // Skip to: 948
/* 917 */     MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 920 */     MCD::OPC_FilterValue, 160, 4, 9, 0, // Skip to: 934
/* 925 */     MCD::OPC_CheckPredicate, 41, 51, 5, // Skip to: 2260
/* 929 */     MCD::OPC_Decode, 207, 3, 254, 1, // Opcode: CVT_S_D64
/* 934 */     MCD::OPC_FilterValue, 160, 5, 41, 5, // Skip to: 2260
/* 939 */     MCD::OPC_CheckPredicate, 41, 37, 5, // Skip to: 2260
/* 943 */     MCD::OPC_Decode, 208, 3, 254, 1, // Opcode: CVT_S_L
/* 948 */     MCD::OPC_FilterValue, 33, 42, 0, // Skip to: 994
/* 952 */     MCD::OPC_ExtractField, 16, 10,  // Inst{25-16} ...
/* 955 */     MCD::OPC_FilterValue, 128, 4, 8, 0, // Skip to: 968
/* 960 */     MCD::OPC_CheckPredicate, 41, 16, 5, // Skip to: 2260
/* 964 */     MCD::OPC_Decode, 198, 3, 93, // Opcode: CVT_D64_S
/* 968 */     MCD::OPC_FilterValue, 128, 5, 8, 0, // Skip to: 981
/* 973 */     MCD::OPC_CheckPredicate, 41, 3, 5, // Skip to: 2260
/* 977 */     MCD::OPC_Decode, 199, 3, 93, // Opcode: CVT_D64_W
/* 981 */     MCD::OPC_FilterValue, 160, 5, 250, 4, // Skip to: 2260
/* 986 */     MCD::OPC_CheckPredicate, 41, 246, 4, // Skip to: 2260
/* 990 */     MCD::OPC_Decode, 197, 3, 100, // Opcode: CVT_D64_L
/* 994 */     MCD::OPC_FilterValue, 36, 16, 0, // Skip to: 1014
/* 998 */     MCD::OPC_CheckPredicate, 41, 234, 4, // Skip to: 2260
/* 1002 */    MCD::OPC_CheckField, 16, 10, 160, 4, 227, 4, // Skip to: 2260
/* 1009 */    MCD::OPC_Decode, 212, 3, 254, 1, // Opcode: CVT_W_D64
/* 1014 */    MCD::OPC_FilterValue, 48, 21, 0, // Skip to: 1039
/* 1018 */    MCD::OPC_CheckPredicate, 44, 214, 4, // Skip to: 2260
/* 1022 */    MCD::OPC_CheckField, 21, 5, 17, 208, 4, // Skip to: 2260
/* 1028 */    MCD::OPC_CheckField, 6, 5, 0, 202, 4, // Skip to: 2260
/* 1034 */    MCD::OPC_Decode, 220, 3, 129, 2, // Opcode: C_F_D64
/* 1039 */    MCD::OPC_FilterValue, 49, 21, 0, // Skip to: 1064
/* 1043 */    MCD::OPC_CheckPredicate, 44, 189, 4, // Skip to: 2260
/* 1047 */    MCD::OPC_CheckField, 21, 5, 17, 183, 4, // Skip to: 2260
/* 1053 */    MCD::OPC_CheckField, 6, 5, 0, 177, 4, // Skip to: 2260
/* 1059 */    MCD::OPC_Decode, 134, 4, 129, 2, // Opcode: C_UN_D64
/* 1064 */    MCD::OPC_FilterValue, 50, 21, 0, // Skip to: 1089
/* 1068 */    MCD::OPC_CheckPredicate, 44, 164, 4, // Skip to: 2260
/* 1072 */    MCD::OPC_CheckField, 21, 5, 17, 158, 4, // Skip to: 2260
/* 1078 */    MCD::OPC_CheckField, 6, 5, 0, 152, 4, // Skip to: 2260
/* 1084 */    MCD::OPC_Decode, 217, 3, 129, 2, // Opcode: C_EQ_D64
/* 1089 */    MCD::OPC_FilterValue, 51, 21, 0, // Skip to: 1114
/* 1093 */    MCD::OPC_CheckPredicate, 44, 139, 4, // Skip to: 2260
/* 1097 */    MCD::OPC_CheckField, 21, 5, 17, 133, 4, // Skip to: 2260
/* 1103 */    MCD::OPC_CheckField, 6, 5, 0, 127, 4, // Skip to: 2260
/* 1109 */    MCD::OPC_Decode, 253, 3, 129, 2, // Opcode: C_UEQ_D64
/* 1114 */    MCD::OPC_FilterValue, 52, 21, 0, // Skip to: 1139
/* 1118 */    MCD::OPC_CheckPredicate, 44, 114, 4, // Skip to: 2260
/* 1122 */    MCD::OPC_CheckField, 21, 5, 17, 108, 4, // Skip to: 2260
/* 1128 */    MCD::OPC_CheckField, 6, 5, 0, 102, 4, // Skip to: 2260
/* 1134 */    MCD::OPC_Decode, 244, 3, 129, 2, // Opcode: C_OLT_D64
/* 1139 */    MCD::OPC_FilterValue, 53, 21, 0, // Skip to: 1164
/* 1143 */    MCD::OPC_CheckPredicate, 44, 89, 4, // Skip to: 2260
/* 1147 */    MCD::OPC_CheckField, 21, 5, 17, 83, 4, // Skip to: 2260
/* 1153 */    MCD::OPC_CheckField, 6, 5, 0, 77, 4, // Skip to: 2260
/* 1159 */    MCD::OPC_Decode, 131, 4, 129, 2, // Opcode: C_ULT_D64
/* 1164 */    MCD::OPC_FilterValue, 54, 21, 0, // Skip to: 1189
/* 1168 */    MCD::OPC_CheckPredicate, 44, 64, 4, // Skip to: 2260
/* 1172 */    MCD::OPC_CheckField, 21, 5, 17, 58, 4, // Skip to: 2260
/* 1178 */    MCD::OPC_CheckField, 6, 5, 0, 52, 4, // Skip to: 2260
/* 1184 */    MCD::OPC_Decode, 241, 3, 129, 2, // Opcode: C_OLE_D64
/* 1189 */    MCD::OPC_FilterValue, 55, 21, 0, // Skip to: 1214
/* 1193 */    MCD::OPC_CheckPredicate, 44, 39, 4, // Skip to: 2260
/* 1197 */    MCD::OPC_CheckField, 21, 5, 17, 33, 4, // Skip to: 2260
/* 1203 */    MCD::OPC_CheckField, 6, 5, 0, 27, 4, // Skip to: 2260
/* 1209 */    MCD::OPC_Decode, 128, 4, 129, 2, // Opcode: C_ULE_D64
/* 1214 */    MCD::OPC_FilterValue, 56, 21, 0, // Skip to: 1239
/* 1218 */    MCD::OPC_CheckPredicate, 44, 14, 4, // Skip to: 2260
/* 1222 */    MCD::OPC_CheckField, 21, 5, 17, 8, 4, // Skip to: 2260
/* 1228 */    MCD::OPC_CheckField, 6, 5, 0, 2, 4, // Skip to: 2260
/* 1234 */    MCD::OPC_Decode, 250, 3, 129, 2, // Opcode: C_SF_D64
/* 1239 */    MCD::OPC_FilterValue, 57, 21, 0, // Skip to: 1264
/* 1243 */    MCD::OPC_CheckPredicate, 44, 245, 3, // Skip to: 2260
/* 1247 */    MCD::OPC_CheckField, 21, 5, 17, 239, 3, // Skip to: 2260
/* 1253 */    MCD::OPC_CheckField, 6, 5, 0, 233, 3, // Skip to: 2260
/* 1259 */    MCD::OPC_Decode, 232, 3, 129, 2, // Opcode: C_NGLE_D64
/* 1264 */    MCD::OPC_FilterValue, 58, 21, 0, // Skip to: 1289
/* 1268 */    MCD::OPC_CheckPredicate, 44, 220, 3, // Skip to: 2260
/* 1272 */    MCD::OPC_CheckField, 21, 5, 17, 214, 3, // Skip to: 2260
/* 1278 */    MCD::OPC_CheckField, 6, 5, 0, 208, 3, // Skip to: 2260
/* 1284 */    MCD::OPC_Decode, 247, 3, 129, 2, // Opcode: C_SEQ_D64
/* 1289 */    MCD::OPC_FilterValue, 59, 21, 0, // Skip to: 1314
/* 1293 */    MCD::OPC_CheckPredicate, 44, 195, 3, // Skip to: 2260
/* 1297 */    MCD::OPC_CheckField, 21, 5, 17, 189, 3, // Skip to: 2260
/* 1303 */    MCD::OPC_CheckField, 6, 5, 0, 183, 3, // Skip to: 2260
/* 1309 */    MCD::OPC_Decode, 235, 3, 129, 2, // Opcode: C_NGL_D64
/* 1314 */    MCD::OPC_FilterValue, 60, 21, 0, // Skip to: 1339
/* 1318 */    MCD::OPC_CheckPredicate, 44, 170, 3, // Skip to: 2260
/* 1322 */    MCD::OPC_CheckField, 21, 5, 17, 164, 3, // Skip to: 2260
/* 1328 */    MCD::OPC_CheckField, 6, 5, 0, 158, 3, // Skip to: 2260
/* 1334 */    MCD::OPC_Decode, 226, 3, 129, 2, // Opcode: C_LT_D64
/* 1339 */    MCD::OPC_FilterValue, 61, 21, 0, // Skip to: 1364
/* 1343 */    MCD::OPC_CheckPredicate, 44, 145, 3, // Skip to: 2260
/* 1347 */    MCD::OPC_CheckField, 21, 5, 17, 139, 3, // Skip to: 2260
/* 1353 */    MCD::OPC_CheckField, 6, 5, 0, 133, 3, // Skip to: 2260
/* 1359 */    MCD::OPC_Decode, 229, 3, 129, 2, // Opcode: C_NGE_D64
/* 1364 */    MCD::OPC_FilterValue, 62, 21, 0, // Skip to: 1389
/* 1368 */    MCD::OPC_CheckPredicate, 44, 120, 3, // Skip to: 2260
/* 1372 */    MCD::OPC_CheckField, 21, 5, 17, 114, 3, // Skip to: 2260
/* 1378 */    MCD::OPC_CheckField, 6, 5, 0, 108, 3, // Skip to: 2260
/* 1384 */    MCD::OPC_Decode, 223, 3, 129, 2, // Opcode: C_LE_D64
/* 1389 */    MCD::OPC_FilterValue, 63, 99, 3, // Skip to: 2260
/* 1393 */    MCD::OPC_CheckPredicate, 44, 95, 3, // Skip to: 2260
/* 1397 */    MCD::OPC_CheckField, 21, 5, 17, 89, 3, // Skip to: 2260
/* 1403 */    MCD::OPC_CheckField, 6, 5, 0, 83, 3, // Skip to: 2260
/* 1409 */    MCD::OPC_Decode, 238, 3, 129, 2, // Opcode: C_NGT_D64
/* 1414 */    MCD::OPC_FilterValue, 18, 41, 0, // Skip to: 1459
/* 1418 */    MCD::OPC_ExtractField, 21, 5,  // Inst{25-21} ...
/* 1421 */    MCD::OPC_FilterValue, 1, 15, 0, // Skip to: 1440
/* 1425 */    MCD::OPC_CheckPredicate, 39, 63, 3, // Skip to: 2260
/* 1429 */    MCD::OPC_CheckField, 3, 8, 0, 57, 3, // Skip to: 2260
/* 1435 */    MCD::OPC_Decode, 179, 4, 251, 1, // Opcode: DMFC2
/* 1440 */    MCD::OPC_FilterValue, 5, 48, 3, // Skip to: 2260
/* 1444 */    MCD::OPC_CheckPredicate, 39, 44, 3, // Skip to: 2260
/* 1448 */    MCD::OPC_CheckField, 3, 8, 0, 38, 3, // Skip to: 2260
/* 1454 */    MCD::OPC_Decode, 184, 4, 251, 1, // Opcode: DMTC2
/* 1459 */    MCD::OPC_FilterValue, 19, 79, 0, // Skip to: 1542
/* 1463 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 1466 */    MCD::OPC_FilterValue, 1, 15, 0, // Skip to: 1485
/* 1470 */    MCD::OPC_CheckPredicate, 45, 18, 3, // Skip to: 2260
/* 1474 */    MCD::OPC_CheckField, 11, 5, 0, 12, 3, // Skip to: 2260
/* 1480 */    MCD::OPC_Decode, 154, 7, 130, 2, // Opcode: LDXC164
/* 1485 */    MCD::OPC_FilterValue, 5, 15, 0, // Skip to: 1504
/* 1489 */    MCD::OPC_CheckPredicate, 46, 255, 2, // Skip to: 2260
/* 1493 */    MCD::OPC_CheckField, 11, 5, 0, 249, 2, // Skip to: 2260
/* 1499 */    MCD::OPC_Decode, 186, 7, 130, 2, // Opcode: LUXC164
/* 1504 */    MCD::OPC_FilterValue, 9, 15, 0, // Skip to: 1523
/* 1508 */    MCD::OPC_CheckPredicate, 45, 236, 2, // Skip to: 2260
/* 1512 */    MCD::OPC_CheckField, 6, 5, 0, 230, 2, // Skip to: 2260
/* 1518 */    MCD::OPC_Decode, 142, 11, 131, 2, // Opcode: SDXC164
/* 1523 */    MCD::OPC_FilterValue, 13, 221, 2, // Skip to: 2260
/* 1527 */    MCD::OPC_CheckPredicate, 46, 217, 2, // Skip to: 2260
/* 1531 */    MCD::OPC_CheckField, 6, 5, 0, 211, 2, // Skip to: 2260
/* 1537 */    MCD::OPC_Decode, 208, 12, 131, 2, // Opcode: SUXC164
/* 1542 */    MCD::OPC_FilterValue, 24, 9, 0, // Skip to: 1555
/* 1546 */    MCD::OPC_CheckPredicate, 38, 198, 2, // Skip to: 2260
/* 1550 */    MCD::OPC_Decode, 141, 4, 132, 2, // Opcode: DADDi
/* 1555 */    MCD::OPC_FilterValue, 25, 9, 0, // Skip to: 1568
/* 1559 */    MCD::OPC_CheckPredicate, 17, 185, 2, // Skip to: 2260
/* 1563 */    MCD::OPC_Decode, 142, 4, 132, 2, // Opcode: DADDiu
/* 1568 */    MCD::OPC_FilterValue, 26, 9, 0, // Skip to: 1581
/* 1572 */    MCD::OPC_CheckPredicate, 38, 172, 2, // Skip to: 2260
/* 1576 */    MCD::OPC_Decode, 150, 7, 212, 1, // Opcode: LDL
/* 1581 */    MCD::OPC_FilterValue, 27, 9, 0, // Skip to: 1594
/* 1585 */    MCD::OPC_CheckPredicate, 38, 159, 2, // Skip to: 2260
/* 1589 */    MCD::OPC_Decode, 152, 7, 212, 1, // Opcode: LDR
/* 1594 */    MCD::OPC_FilterValue, 28, 159, 1, // Skip to: 2013
/* 1598 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 1601 */    MCD::OPC_FilterValue, 3, 15, 0, // Skip to: 1620
/* 1605 */    MCD::OPC_CheckPredicate, 47, 139, 2, // Skip to: 2260
/* 1609 */    MCD::OPC_CheckField, 6, 5, 0, 133, 2, // Skip to: 2260
/* 1615 */    MCD::OPC_Decode, 187, 4, 219, 1, // Opcode: DMUL
/* 1620 */    MCD::OPC_FilterValue, 8, 15, 0, // Skip to: 1639
/* 1624 */    MCD::OPC_CheckPredicate, 47, 120, 2, // Skip to: 2260
/* 1628 */    MCD::OPC_CheckField, 6, 15, 0, 114, 2, // Skip to: 2260
/* 1634 */    MCD::OPC_Decode, 160, 9, 133, 2, // Opcode: MTM0
/* 1639 */    MCD::OPC_FilterValue, 9, 15, 0, // Skip to: 1658
/* 1643 */    MCD::OPC_CheckPredicate, 47, 101, 2, // Skip to: 2260
/* 1647 */    MCD::OPC_CheckField, 6, 15, 0, 95, 2, // Skip to: 2260
/* 1653 */    MCD::OPC_Decode, 163, 9, 133, 2, // Opcode: MTP0
/* 1658 */    MCD::OPC_FilterValue, 10, 15, 0, // Skip to: 1677
/* 1662 */    MCD::OPC_CheckPredicate, 47, 82, 2, // Skip to: 2260
/* 1666 */    MCD::OPC_CheckField, 6, 15, 0, 76, 2, // Skip to: 2260
/* 1672 */    MCD::OPC_Decode, 164, 9, 133, 2, // Opcode: MTP1
/* 1677 */    MCD::OPC_FilterValue, 11, 15, 0, // Skip to: 1696
/* 1681 */    MCD::OPC_CheckPredicate, 47, 63, 2, // Skip to: 2260
/* 1685 */    MCD::OPC_CheckField, 6, 15, 0, 57, 2, // Skip to: 2260
/* 1691 */    MCD::OPC_Decode, 165, 9, 133, 2, // Opcode: MTP2
/* 1696 */    MCD::OPC_FilterValue, 12, 15, 0, // Skip to: 1715
/* 1700 */    MCD::OPC_CheckPredicate, 47, 44, 2, // Skip to: 2260
/* 1704 */    MCD::OPC_CheckField, 6, 15, 0, 38, 2, // Skip to: 2260
/* 1710 */    MCD::OPC_Decode, 161, 9, 133, 2, // Opcode: MTM1
/* 1715 */    MCD::OPC_FilterValue, 13, 15, 0, // Skip to: 1734
/* 1719 */    MCD::OPC_CheckPredicate, 47, 25, 2, // Skip to: 2260
/* 1723 */    MCD::OPC_CheckField, 6, 15, 0, 19, 2, // Skip to: 2260
/* 1729 */    MCD::OPC_Decode, 162, 9, 133, 2, // Opcode: MTM2
/* 1734 */    MCD::OPC_FilterValue, 15, 15, 0, // Skip to: 1753
/* 1738 */    MCD::OPC_CheckPredicate, 47, 6, 2, // Skip to: 2260
/* 1742 */    MCD::OPC_CheckField, 6, 5, 0, 0, 2, // Skip to: 2260
/* 1748 */    MCD::OPC_Decode, 200, 13, 219, 1, // Opcode: VMULU
/* 1753 */    MCD::OPC_FilterValue, 16, 15, 0, // Skip to: 1772
/* 1757 */    MCD::OPC_CheckPredicate, 47, 243, 1, // Skip to: 2260
/* 1761 */    MCD::OPC_CheckField, 6, 5, 0, 237, 1, // Skip to: 2260
/* 1767 */    MCD::OPC_Decode, 199, 13, 219, 1, // Opcode: VMM0
/* 1772 */    MCD::OPC_FilterValue, 17, 15, 0, // Skip to: 1791
/* 1776 */    MCD::OPC_CheckPredicate, 47, 224, 1, // Skip to: 2260
/* 1780 */    MCD::OPC_CheckField, 6, 5, 0, 218, 1, // Skip to: 2260
/* 1786 */    MCD::OPC_Decode, 198, 13, 219, 1, // Opcode: V3MULU
/* 1791 */    MCD::OPC_FilterValue, 36, 15, 0, // Skip to: 1810
/* 1795 */    MCD::OPC_CheckPredicate, 48, 205, 1, // Skip to: 2260
/* 1799 */    MCD::OPC_CheckField, 6, 5, 0, 199, 1, // Skip to: 2260
/* 1805 */    MCD::OPC_Decode, 151, 4, 134, 2, // Opcode: DCLZ
/* 1810 */    MCD::OPC_FilterValue, 37, 15, 0, // Skip to: 1829
/* 1814 */    MCD::OPC_CheckPredicate, 48, 186, 1, // Skip to: 2260
/* 1818 */    MCD::OPC_CheckField, 6, 5, 0, 180, 1, // Skip to: 2260
/* 1824 */    MCD::OPC_Decode, 149, 4, 134, 2, // Opcode: DCLO
/* 1829 */    MCD::OPC_FilterValue, 40, 15, 0, // Skip to: 1848
/* 1833 */    MCD::OPC_CheckPredicate, 47, 167, 1, // Skip to: 2260
/* 1837 */    MCD::OPC_CheckField, 6, 5, 0, 161, 1, // Skip to: 2260
/* 1843 */    MCD::OPC_Decode, 164, 1, 219, 1, // Opcode: BADDu
/* 1848 */    MCD::OPC_FilterValue, 42, 15, 0, // Skip to: 1867
/* 1852 */    MCD::OPC_CheckPredicate, 47, 148, 1, // Skip to: 2260
/* 1856 */    MCD::OPC_CheckField, 6, 5, 0, 142, 1, // Skip to: 2260
/* 1862 */    MCD::OPC_Decode, 159, 11, 219, 1, // Opcode: SEQ
/* 1867 */    MCD::OPC_FilterValue, 43, 15, 0, // Skip to: 1886
/* 1871 */    MCD::OPC_CheckPredicate, 47, 129, 1, // Skip to: 2260
/* 1875 */    MCD::OPC_CheckField, 6, 5, 0, 123, 1, // Skip to: 2260
/* 1881 */    MCD::OPC_Decode, 227, 11, 219, 1, // Opcode: SNE
/* 1886 */    MCD::OPC_FilterValue, 44, 20, 0, // Skip to: 1910
/* 1890 */    MCD::OPC_CheckPredicate, 47, 110, 1, // Skip to: 2260
/* 1894 */    MCD::OPC_CheckField, 16, 5, 0, 104, 1, // Skip to: 2260
/* 1900 */    MCD::OPC_CheckField, 6, 5, 0, 98, 1, // Skip to: 2260
/* 1906 */    MCD::OPC_Decode, 138, 10, 58, // Opcode: POP
/* 1910 */    MCD::OPC_FilterValue, 45, 21, 0, // Skip to: 1935
/* 1914 */    MCD::OPC_CheckPredicate, 47, 86, 1, // Skip to: 2260
/* 1918 */    MCD::OPC_CheckField, 16, 5, 0, 80, 1, // Skip to: 2260
/* 1924 */    MCD::OPC_CheckField, 6, 5, 0, 74, 1, // Skip to: 2260
/* 1930 */    MCD::OPC_Decode, 212, 4, 217, 1, // Opcode: DPOP
/* 1935 */    MCD::OPC_FilterValue, 46, 9, 0, // Skip to: 1948
/* 1939 */    MCD::OPC_CheckPredicate, 47, 61, 1, // Skip to: 2260
/* 1943 */    MCD::OPC_Decode, 160, 11, 135, 2, // Opcode: SEQi
/* 1948 */    MCD::OPC_FilterValue, 47, 9, 0, // Skip to: 1961
/* 1952 */    MCD::OPC_CheckPredicate, 47, 48, 1, // Skip to: 2260
/* 1956 */    MCD::OPC_Decode, 228, 11, 135, 2, // Opcode: SNEi
/* 1961 */    MCD::OPC_FilterValue, 50, 9, 0, // Skip to: 1974
/* 1965 */    MCD::OPC_CheckPredicate, 47, 35, 1, // Skip to: 2260
/* 1969 */    MCD::OPC_Decode, 222, 2, 136, 2, // Opcode: CINS
/* 1974 */    MCD::OPC_FilterValue, 51, 9, 0, // Skip to: 1987
/* 1978 */    MCD::OPC_CheckPredicate, 47, 22, 1, // Skip to: 2260
/* 1982 */    MCD::OPC_Decode, 223, 2, 136, 2, // Opcode: CINS32
/* 1987 */    MCD::OPC_FilterValue, 58, 9, 0, // Skip to: 2000
/* 1991 */    MCD::OPC_CheckPredicate, 47, 9, 1, // Skip to: 2260
/* 1995 */    MCD::OPC_Decode, 139, 5, 136, 2, // Opcode: EXTS
/* 2000 */    MCD::OPC_FilterValue, 59, 0, 1, // Skip to: 2260
/* 2004 */    MCD::OPC_CheckPredicate, 47, 252, 0, // Skip to: 2260
/* 2008 */    MCD::OPC_Decode, 140, 5, 136, 2, // Opcode: EXTS32
/* 2013 */    MCD::OPC_FilterValue, 31, 126, 0, // Skip to: 2143
/* 2017 */    MCD::OPC_ExtractField, 0, 6,  // Inst{5-0} ...
/* 2020 */    MCD::OPC_FilterValue, 1, 9, 0, // Skip to: 2033
/* 2024 */    MCD::OPC_CheckPredicate, 4, 232, 0, // Skip to: 2260
/* 2028 */    MCD::OPC_Decode, 158, 4, 137, 2, // Opcode: DEXTM
/* 2033 */    MCD::OPC_FilterValue, 2, 9, 0, // Skip to: 2046
/* 2037 */    MCD::OPC_CheckPredicate, 4, 219, 0, // Skip to: 2260
/* 2041 */    MCD::OPC_Decode, 159, 4, 137, 2, // Opcode: DEXTU
/* 2046 */    MCD::OPC_FilterValue, 3, 9, 0, // Skip to: 2059
/* 2050 */    MCD::OPC_CheckPredicate, 4, 206, 0, // Skip to: 2260
/* 2054 */    MCD::OPC_Decode, 157, 4, 137, 2, // Opcode: DEXT
/* 2059 */    MCD::OPC_FilterValue, 5, 9, 0, // Skip to: 2072
/* 2063 */    MCD::OPC_CheckPredicate, 4, 193, 0, // Skip to: 2260
/* 2067 */    MCD::OPC_Decode, 162, 4, 138, 2, // Opcode: DINSM
/* 2072 */    MCD::OPC_FilterValue, 6, 9, 0, // Skip to: 2085
/* 2076 */    MCD::OPC_CheckPredicate, 4, 180, 0, // Skip to: 2260
/* 2080 */    MCD::OPC_Decode, 163, 4, 138, 2, // Opcode: DINSU
/* 2085 */    MCD::OPC_FilterValue, 7, 9, 0, // Skip to: 2098
/* 2089 */    MCD::OPC_CheckPredicate, 4, 167, 0, // Skip to: 2260
/* 2093 */    MCD::OPC_Decode, 161, 4, 138, 2, // Opcode: DINS
/* 2098 */    MCD::OPC_FilterValue, 36, 158, 0, // Skip to: 2260
/* 2102 */    MCD::OPC_ExtractField, 6, 5,  // Inst{10-6} ...
/* 2105 */    MCD::OPC_FilterValue, 2, 15, 0, // Skip to: 2124
/* 2109 */    MCD::OPC_CheckPredicate, 37, 147, 0, // Skip to: 2260
/* 2113 */    MCD::OPC_CheckField, 21, 5, 0, 141, 0, // Skip to: 2260
/* 2119 */    MCD::OPC_Decode, 230, 4, 238, 1, // Opcode: DSBH
/* 2124 */    MCD::OPC_FilterValue, 5, 132, 0, // Skip to: 2260
/* 2128 */    MCD::OPC_CheckPredicate, 37, 128, 0, // Skip to: 2260
/* 2132 */    MCD::OPC_CheckField, 21, 5, 0, 122, 0, // Skip to: 2260
/* 2138 */    MCD::OPC_Decode, 232, 4, 238, 1, // Opcode: DSHD
/* 2143 */    MCD::OPC_FilterValue, 39, 9, 0, // Skip to: 2156
/* 2147 */    MCD::OPC_CheckPredicate, 17, 109, 0, // Skip to: 2260
/* 2151 */    MCD::OPC_Decode, 217, 7, 212, 1, // Opcode: LWu
/* 2156 */    MCD::OPC_FilterValue, 44, 9, 0, // Skip to: 2169
/* 2160 */    MCD::OPC_CheckPredicate, 38, 96, 0, // Skip to: 2260
/* 2164 */    MCD::OPC_Decode, 139, 11, 212, 1, // Opcode: SDL
/* 2169 */    MCD::OPC_FilterValue, 45, 9, 0, // Skip to: 2182
/* 2173 */    MCD::OPC_CheckPredicate, 38, 83, 0, // Skip to: 2260
/* 2177 */    MCD::OPC_Decode, 140, 11, 212, 1, // Opcode: SDR
/* 2182 */    MCD::OPC_FilterValue, 52, 9, 0, // Skip to: 2195
/* 2186 */    MCD::OPC_CheckPredicate, 38, 70, 0, // Skip to: 2260
/* 2190 */    MCD::OPC_Decode, 172, 7, 212, 1, // Opcode: LLD
/* 2195 */    MCD::OPC_FilterValue, 53, 9, 0, // Skip to: 2208
/* 2199 */    MCD::OPC_CheckPredicate, 49, 57, 0, // Skip to: 2260
/* 2203 */    MCD::OPC_Decode, 141, 7, 214, 1, // Opcode: LDC164
/* 2208 */    MCD::OPC_FilterValue, 55, 9, 0, // Skip to: 2221
/* 2212 */    MCD::OPC_CheckPredicate, 17, 44, 0, // Skip to: 2260
/* 2216 */    MCD::OPC_Decode, 139, 7, 212, 1, // Opcode: LD
/* 2221 */    MCD::OPC_FilterValue, 60, 9, 0, // Skip to: 2234
/* 2225 */    MCD::OPC_CheckPredicate, 38, 31, 0, // Skip to: 2260
/* 2229 */    MCD::OPC_Decode, 250, 10, 212, 1, // Opcode: SCD
/* 2234 */    MCD::OPC_FilterValue, 61, 9, 0, // Skip to: 2247
/* 2238 */    MCD::OPC_CheckPredicate, 49, 18, 0, // Skip to: 2260
/* 2242 */    MCD::OPC_Decode, 132, 11, 214, 1, // Opcode: SDC164
/* 2247 */    MCD::OPC_FilterValue, 63, 9, 0, // Skip to: 2260
/* 2251 */    MCD::OPC_CheckPredicate, 17, 5, 0, // Skip to: 2260
/* 2255 */    MCD::OPC_Decode, 254, 10, 212, 1, // Opcode: SD
/* 2260 */    MCD::OPC_Fail,
  0
};

static bool checkDecoderPredicate(unsigned Idx, uint64_t Bits) {
  switch (Idx) {
  default: llvm_unreachable("Invalid index!");
  case 0:
    return ((Bits & Mips::FeatureMips16));
  case 1:
    return (!(Bits & Mips::FeatureMips16));
  case 2:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips2));
  case 3:
    return ((Bits & Mips::FeatureMicroMips));
  case 4:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32r2));
  case 5:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureMicroMips));
  case 6:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips4_32) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 7:
    return ((Bits & Mips::FeatureMSA));
  case 8:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 9:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32));
  case 10:
    return (!(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6) && !(Bits & Mips::FeatureMicroMips));
  case 11:
    return ((Bits & Mips::FeatureDSP));
  case 12:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 13:
    return ((Bits & Mips::FeatureMSA) && (Bits & Mips::FeatureMips64));
  case 14:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 15:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips3_32));
  case 16:
    return (!(Bits & Mips::FeatureMicroMips));
  case 17:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips3));
  case 18:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32r2) && !(Bits & Mips::FeatureFP64Bit));
  case 19:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureFP64Bit));
  case 20:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips3_32r2));
  case 21:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips2) && !(Bits & Mips::FeatureFP64Bit));
  case 22:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips4_32) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 23:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6) && !(Bits & Mips::FeatureFP64Bit));
  case 24:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips4_32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 25:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips4_32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6) && !(Bits & Mips::FeatureMicroMips));
  case 26:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips5_32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 27:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 28:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 29:
    return ((Bits & Mips::FeatureDSPR2));
  case 30:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips3_32) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 31:
    return ((Bits & Mips::FeatureMips2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6) && !(Bits & Mips::FeatureMicroMips));
  case 32:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips2));
  case 33:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32r6));
  case 34:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips64r6));
  case 35:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureGP64Bit) && (Bits & Mips::FeatureMips32r6));
  case 36:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureGP64Bit) && (Bits & Mips::FeatureMips32r6));
  case 37:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips64r2));
  case 38:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips3) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 39:
    return ((Bits & Mips::FeatureMips64));
  case 40:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips32r2) && (Bits & Mips::FeatureFP64Bit));
  case 41:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureFP64Bit));
  case 42:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips2) && (Bits & Mips::FeatureFP64Bit));
  case 43:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips4_32) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 44:
    return (!(Bits & Mips::FeatureMips16) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6) && (Bits & Mips::FeatureFP64Bit));
  case 45:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips4_32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 46:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips5_32r2) && !(Bits & Mips::FeatureMips32r6) && !(Bits & Mips::FeatureMips64r6));
  case 47:
    return ((Bits & Mips::FeatureCnMips));
  case 48:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureMips64) && !(Bits & Mips::FeatureMips64r6));
  case 49:
    return (!(Bits & Mips::FeatureMips16) && (Bits & Mips::FeatureFP64Bit) && (Bits & Mips::FeatureMips2));
  }
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
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 2:
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 3:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 3, 2) << 3;
    tmp |= fieldFromInstruction(insn, 5, 3) << 0;
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 4:
    tmp = fieldFromInstruction(insn, 0, 4);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 5:
    tmp = fieldFromInstruction(insn, 2, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 5, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 6:
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 5, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 7:
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 8, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 5, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 8:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 5) << 0;
    tmp |= fieldFromInstruction(insn, 16, 5) << 11;
    tmp |= fieldFromInstruction(insn, 21, 6) << 5;
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 9:
    tmp = fieldFromInstruction(insn, 5, 3);
    if (DecodeCPU16RegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 10:
    if (DecodeFMem3(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 11:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 4, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 12:
    if (DecodeMemMMImm4(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 13:
    tmp = fieldFromInstruction(insn, 5, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 14:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 4, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 15:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 4, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 4);
    if (DecodeANDI16Imm(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 16:
    tmp = fieldFromInstruction(insn, 3, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 17:
    tmp = fieldFromInstruction(insn, 3, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 3, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 18:
    tmp = fieldFromInstruction(insn, 4, 2);
    if (DecodeRegListOperand16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 19:
    tmp = fieldFromInstruction(insn, 0, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 20:
    tmp = fieldFromInstruction(insn, 0, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 21:
    tmp = fieldFromInstruction(insn, 0, 5);
    if (DecodeUImm5lsl2(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 22:
    if (DecodeMemMMSPImm5Lsl2(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 23:
    tmp = fieldFromInstruction(insn, 5, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 5, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 4);
    if (DecodeSimm4(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 24:
    tmp = fieldFromInstruction(insn, 1, 9);
    if (DecodeSimm9SP(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 25:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 4, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 3);
    if (DecodeAddiur2Simm7(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 26:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 1, 6);
    if (DecodeUImm6Lsl2(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 27:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 7);
    if (DecodeBranchTarget7MM(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 28:
    tmp = fieldFromInstruction(insn, 7, 3);
    if (DecodeGPRMM16RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 7);
    if (DecodeLiSimm7(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 29:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 30:
    tmp = fieldFromInstruction(insn, 16, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 6, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 31:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeInsSize(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 32:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 33:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 34:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 35:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 36:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeExtSize(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 37:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 12, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 38:
    tmp = fieldFromInstruction(insn, 16, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 39:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 40:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 41:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeHWRegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 42:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 43:
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 44:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 45:
    if (DecodeMemMMImm16(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 46:
    if (DecodeMemMMImm12(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 47:
    if (DecodeCacheOpMM(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 48:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTargetMM(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 49:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 50:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 51:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 13, 3);
    if (DecodeFCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 52:
    if (DecodeJumpTargetMM(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 53:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTargetMM(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 54:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 55:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 18, 3);
    if (DecodeFCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 56:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 2);
    if (DecodeLSAImm(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 57:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 58:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 59:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 60:
    tmp = fieldFromInstruction(insn, 6, 20);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 61:
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 62:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 63:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 64:
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeHI32DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 65:
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeLO32DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 66:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 2);
    if (DecodeLSAImm(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 67:
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 68:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 69:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 70:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 71:
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 72:
    if (DecodeSyncI(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 73:
    if (DecodeJumpTarget(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 74:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 75:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 76:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 77:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 78:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 79:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 80:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeCCRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 81:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 82:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 83:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 84:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeCCRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 85:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 86:
    tmp = fieldFromInstruction(insn, 18, 3);
    if (DecodeFCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 87:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 88:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 89:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 90:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 18, 3);
    if (DecodeFCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 91:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 92:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 93:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 94:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 95:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 96:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 97:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 98:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 18, 3);
    if (DecodeFCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 99:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 100:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 101:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 102:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 103:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 104:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 105:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 106:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 107:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 108:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 109:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 110:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeAFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 111:
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 112:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 113:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 8);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 114:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 8);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 115:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 8);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 116:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 8);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 117:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 118:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 119:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 120:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 121:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 122:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 123:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 124:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 125:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 6);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 126:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 127:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 128:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 6);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 129:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 130:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 131:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 132:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 133:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 134:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 135:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 136:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 137:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 138:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 139:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 140:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 141:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 142:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 143:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 144:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 145:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 146:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 147:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 148:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 149:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 150:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 151:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 152:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 153:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 154:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 155:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 156:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 157:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 158:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSACtrlRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 159:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 160:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 161:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 162:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 163:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSACtrlRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 164:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 165:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 166:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 167:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 168:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 169:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 4);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 170:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 171:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 172:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 1);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 173:
    if (DecodeINSVE_DF(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 174:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 175:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 176:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128BRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 177:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 178:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 179:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 180:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 181:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 182:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 183:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128HRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 184:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeMSA128DRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeMSA128WRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 185:
    if (DecodeMSA128Mem(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 186:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeExtSize(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 187:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeInsSize(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 188:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 189:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 190:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 191:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 192:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 193:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 194:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 195:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 196:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 197:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 198:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 199:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 200:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 201:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 202:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeDSPRRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 203:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 204:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 205:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 206:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 207:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 208:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 209:
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 20, 6);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 210:
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 2);
    if (DecodeACC64DSPRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 211:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeHWRegsRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 212:
    if (DecodeMem(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 213:
    if (DecodeCacheOp(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 214:
    if (DecodeFMem(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 215:
    if (DecodeFMem2(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 216:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 217:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 218:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 2);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 219:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 220:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 221:
    if (DecodeBlezGroupBranch(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 222:
    if (DecodeBgtzGroupBranch(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 223:
    if (DecodeAddiGroupBranch(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 224:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 225:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGRCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 226:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 227:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGRCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 228:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 229:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 230:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGRCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 231:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGRCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 232:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeCOP2RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeBranchTarget(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 233:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeCOP2RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 0, 11) << 0;
    tmp |= fieldFromInstruction(insn, 11, 5) << 16;
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 234:
    if (DecodeBlezlGroupBranch(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 235:
    if (DecodeBgtzlGroupBranch(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 236:
    if (DecodeDaddiGroupBranch(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 237:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 238:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 239:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 240:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 7, 9) << 0;
    tmp |= fieldFromInstruction(insn, 21, 5) << 16;
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 16, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 241:
    if (DecodeSpecial3LlSc(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 242:
    tmp = fieldFromInstruction(insn, 0, 26);
    if (DecodeBranchTarget26(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 243:
    if (DecodeSimm16(MI, insn, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 244:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 21);
    if (DecodeBranchTarget21(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 245:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 19);
    if (DecodeSimm19Lsl2(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 246:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 18);
    if (DecodeSimm18Lsl3(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 247:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 248:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 249:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 250:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 251:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 3);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 252:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 253:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 254:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 255:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 18, 3);
    if (DecodeFCCRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 256:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR32RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 257:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 258:
    tmp = fieldFromInstruction(insn, 6, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 259:
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeFGR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodePtrRegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 260:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 0, 16);
    if (DecodeSimm16(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 261:
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 262:
    tmp = 0;
    tmp |= fieldFromInstruction(insn, 11, 5) << 0;
    tmp |= fieldFromInstruction(insn, 16, 5) << 0;
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 263:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 10);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 264:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    return S;
  case 265:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeExtSize(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    return S;
  case 266:
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 21, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 6, 5);
    MI.addOperand(MCOperand::CreateImm(tmp));
    tmp = fieldFromInstruction(insn, 11, 5);
    if (DecodeInsSize(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
    tmp = fieldFromInstruction(insn, 16, 5);
    if (DecodeGPR64RegisterClass(MI, tmp, Address, Decoder) == MCDisassembler::Fail) return MCDisassembler::Fail;
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
