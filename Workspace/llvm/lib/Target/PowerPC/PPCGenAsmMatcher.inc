/*===- TableGen'erated file -------------------------------------*- C++ -*-===*\
|*                                                                            *|
|*Assembly Matcher Source Fragment                                            *|
|*                                                                            *|
|* Automatically generated file, do not edit!                                 *|
|*                                                                            *|
\*===----------------------------------------------------------------------===*/


#ifdef GET_ASSEMBLER_HEADER
#undef GET_ASSEMBLER_HEADER
  // This should be included into the middle of the declaration of
  // your subclasses implementation of MCTargetAsmParser.
  uint64_t ComputeAvailableFeatures(uint64_t FeatureBits) const;
  void convertToMCInst(unsigned Kind, MCInst &Inst, unsigned Opcode,
                       const OperandVector &Operands);
  void convertToMapAndConstraints(unsigned Kind,
                           const OperandVector &Operands) override;
  bool mnemonicIsValid(StringRef Mnemonic, unsigned VariantID) override;
  unsigned MatchInstructionImpl(const OperandVector &Operands,
                                MCInst &Inst,
                                uint64_t &ErrorInfo, bool matchingInlineAsm,
                                unsigned VariantID = 0);
#endif // GET_ASSEMBLER_HEADER_INFO


#ifdef GET_OPERAND_DIAGNOSTIC_TYPES
#undef GET_OPERAND_DIAGNOSTIC_TYPES

#endif // GET_OPERAND_DIAGNOSTIC_TYPES


#ifdef GET_REGISTER_MATCHER
#undef GET_REGISTER_MATCHER

// Flags for subtarget features that participate in instruction matching.
enum SubtargetFeatureFlag : uint8_t {
  Feature_None = 0
};

#endif // GET_REGISTER_MATCHER


#ifdef GET_SUBTARGET_FEATURE_NAME
#undef GET_SUBTARGET_FEATURE_NAME

// User-level names for subtarget features that participate in
// instruction matching.
static const char *getSubtargetFeatureName(uint64_t Val) {
  return "(unknown)";
}

#endif // GET_SUBTARGET_FEATURE_NAME


#ifdef GET_MATCHER_IMPLEMENTATION
#undef GET_MATCHER_IMPLEMENTATION

namespace {
enum OperatorConversionKind {
  CVT_Done,
  CVT_Reg,
  CVT_Tied,
  CVT_95_addRegG8RCOperands,
  CVT_95_addTLSRegOperands,
  CVT_95_addRegGPRCOperands,
  CVT_95_addRegGPRCNoR0Operands,
  CVT_95_addS16ImmOperands,
  CVT_95_addU16ImmOperands,
  CVT_95_addBranchTargetOperands,
  CVT_95_addImmOperands,
  CVT_95_addRegCRBITRCOperands,
  CVT_imm_0,
  CVT_imm_8,
  CVT_imm_2,
  CVT_imm_10,
  CVT_imm_76,
  CVT_regCR0,
  CVT_95_addRegCRRCOperands,
  CVT_imm_79,
  CVT_imm_78,
  CVT_imm_4,
  CVT_imm_7,
  CVT_imm_6,
  CVT_imm_44,
  CVT_imm_47,
  CVT_imm_46,
  CVT_imm_36,
  CVT_imm_39,
  CVT_imm_38,
  CVT_imm_12,
  CVT_imm_15,
  CVT_imm_14,
  CVT_imm_68,
  CVT_imm_71,
  CVT_imm_70,
  CVT_imm_100,
  CVT_imm_103,
  CVT_imm_102,
  CVT_imm_108,
  CVT_imm_111,
  CVT_imm_110,
  CVT_imm_31,
  CVT_95_addRegGxRCNoR0Operands,
  CVT_95_addRegGxRCOperands,
  CVT_regR0,
  CVT_95_addRegF4RCOperands,
  CVT_95_addRegF8RCOperands,
  CVT_95_addRegVRRCOperands,
  CVT_imm_1,
  CVT_95_addRegVSFRCOperands,
  CVT_95_addRegVSRCOperands,
  CVT_imm_29,
  CVT_imm_280,
  CVT_imm_128,
  CVT_imm_129,
  CVT_imm_130,
  CVT_imm_131,
  CVT_imm_132,
  CVT_imm_133,
  CVT_imm_134,
  CVT_imm_135,
  CVT_imm_28,
  CVT_imm_19,
  CVT_imm_537,
  CVT_imm_539,
  CVT_imm_541,
  CVT_imm_543,
  CVT_imm_536,
  CVT_imm_538,
  CVT_imm_540,
  CVT_imm_542,
  CVT_imm_1018,
  CVT_imm_981,
  CVT_imm_22,
  CVT_imm_17,
  CVT_imm_18,
  CVT_imm_980,
  CVT_imm_529,
  CVT_imm_531,
  CVT_imm_533,
  CVT_imm_535,
  CVT_imm_528,
  CVT_imm_530,
  CVT_imm_532,
  CVT_imm_534,
  CVT_imm_1019,
  CVT_95_addCRBitMaskOperands,
  CVT_imm_48,
  CVT_imm_287,
  CVT_imm_5,
  CVT_imm_25,
  CVT_imm_512,
  CVT_imm_272,
  CVT_imm_273,
  CVT_imm_274,
  CVT_imm_275,
  CVT_imm_260,
  CVT_imm_261,
  CVT_imm_262,
  CVT_imm_263,
  CVT_imm_26,
  CVT_imm_27,
  CVT_imm_990,
  CVT_imm_991,
  CVT_imm_268,
  CVT_imm_988,
  CVT_imm_989,
  CVT_imm_269,
  CVT_imm_986,
  CVT_imm_255,
  CVT_imm_284,
  CVT_imm_285,
  CVT_imm_20,
  CVT_imm_16,
  CVT_imm_24,
  CVT_imm_3,
  CVT_NUM_CONVERTERS
};

enum InstructionConversionKind {
  Convert__RegG8RC1_0__RegG8RC1_1__TLSReg1_2,
  Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2,
  Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3,
  Convert__RegGPRC1_0__RegGPRCNoR01_1__S16Imm1_2,
  Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2,
  Convert__RegGPRC1_1__RegGPRC1_2__S16Imm1_3,
  Convert__RegGPRC1_0__RegGPRCNoR01_1__S17Imm1_2,
  Convert__RegGPRC1_0__RegGPRC1_1,
  Convert__RegGPRC1_1__RegGPRC1_2,
  Convert__RegGPRC1_1__RegGPRC1_2__U16Imm1_3,
  Convert_NoOperands,
  Convert__DirectBr1_0,
  Convert__U5Imm1_0__RegCRBITRC1_1__CondBr1_2,
  Convert__U5Imm1_0__RegCRBITRC1_1__imm_0,
  Convert__U5Imm1_0__RegCRBITRC1_1__Imm1_2,
  Convert__CondBr1_0,
  Convert__imm_0__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_0__RegCRBITRC1_0__imm_0,
  Convert__imm_8__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_8__RegCRBITRC1_0__imm_0,
  Convert__imm_2__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_2__RegCRBITRC1_0__imm_0,
  Convert__imm_10__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_10__RegCRBITRC1_0__imm_0,
  Convert__imm_76__regCR0__CondBr1_0,
  Convert__imm_76__RegCRRC1_0__CondBr1_1,
  Convert__imm_79__regCR0__CondBr1_0,
  Convert__imm_79__RegCRRC1_0__CondBr1_1,
  Convert__imm_78__regCR0__CondBr1_0,
  Convert__imm_78__RegCRRC1_0__CondBr1_1,
  Convert__imm_76__regCR0,
  Convert__imm_76__RegCRRC1_0,
  Convert__imm_79__regCR0,
  Convert__imm_79__RegCRRC1_0,
  Convert__imm_78__regCR0,
  Convert__imm_78__RegCRRC1_0,
  Convert__imm_4__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_7__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_6__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_4__RegCRBITRC1_0__imm_0,
  Convert__imm_7__RegCRBITRC1_0__imm_0,
  Convert__imm_6__RegCRBITRC1_0__imm_0,
  Convert__imm_4__regCR0__CondBr1_0,
  Convert__imm_4__RegCRRC1_0__CondBr1_1,
  Convert__imm_7__regCR0__CondBr1_0,
  Convert__imm_7__RegCRRC1_0__CondBr1_1,
  Convert__imm_6__regCR0__CondBr1_0,
  Convert__imm_6__RegCRRC1_0__CondBr1_1,
  Convert__imm_4__regCR0,
  Convert__imm_4__RegCRRC1_0,
  Convert__imm_7__regCR0,
  Convert__imm_7__RegCRRC1_0,
  Convert__imm_6__regCR0,
  Convert__imm_6__RegCRRC1_0,
  Convert__imm_44__regCR0__CondBr1_0,
  Convert__imm_44__RegCRRC1_0__CondBr1_1,
  Convert__imm_47__regCR0__CondBr1_0,
  Convert__imm_47__RegCRRC1_0__CondBr1_1,
  Convert__imm_46__regCR0__CondBr1_0,
  Convert__imm_46__RegCRRC1_0__CondBr1_1,
  Convert__imm_44__regCR0,
  Convert__imm_44__RegCRRC1_0,
  Convert__imm_47__regCR0,
  Convert__imm_47__RegCRRC1_0,
  Convert__imm_46__regCR0,
  Convert__imm_46__RegCRRC1_0,
  Convert__DirectBr1_0__Imm1_1,
  Convert__imm_36__regCR0__CondBr1_0,
  Convert__imm_36__RegCRRC1_0__CondBr1_1,
  Convert__imm_39__regCR0__CondBr1_0,
  Convert__imm_39__RegCRRC1_0__CondBr1_1,
  Convert__imm_38__regCR0__CondBr1_0,
  Convert__imm_38__RegCRRC1_0__CondBr1_1,
  Convert__imm_36__regCR0,
  Convert__imm_36__RegCRRC1_0,
  Convert__imm_39__regCR0,
  Convert__imm_39__RegCRRC1_0,
  Convert__imm_38__regCR0,
  Convert__imm_38__RegCRRC1_0,
  Convert__imm_12__regCR0__CondBr1_0,
  Convert__imm_12__RegCRRC1_0__CondBr1_1,
  Convert__imm_15__regCR0__CondBr1_0,
  Convert__imm_15__RegCRRC1_0__CondBr1_1,
  Convert__imm_14__regCR0__CondBr1_0,
  Convert__imm_14__RegCRRC1_0__CondBr1_1,
  Convert__imm_12__regCR0,
  Convert__imm_12__RegCRRC1_0,
  Convert__imm_15__regCR0,
  Convert__imm_15__RegCRRC1_0,
  Convert__imm_14__regCR0,
  Convert__imm_14__RegCRRC1_0,
  Convert__imm_68__regCR0__CondBr1_0,
  Convert__imm_68__RegCRRC1_0__CondBr1_1,
  Convert__imm_71__regCR0__CondBr1_0,
  Convert__imm_71__RegCRRC1_0__CondBr1_1,
  Convert__imm_70__regCR0__CondBr1_0,
  Convert__imm_70__RegCRRC1_0__CondBr1_1,
  Convert__imm_68__regCR0,
  Convert__imm_68__RegCRRC1_0,
  Convert__imm_71__regCR0,
  Convert__imm_71__RegCRRC1_0,
  Convert__imm_70__regCR0,
  Convert__imm_70__RegCRRC1_0,
  Convert__imm_100__regCR0__CondBr1_0,
  Convert__imm_100__RegCRRC1_0__CondBr1_1,
  Convert__imm_103__regCR0__CondBr1_0,
  Convert__imm_103__RegCRRC1_0__CondBr1_1,
  Convert__imm_102__regCR0__CondBr1_0,
  Convert__imm_102__RegCRRC1_0__CondBr1_1,
  Convert__imm_100__regCR0,
  Convert__imm_100__RegCRRC1_0,
  Convert__imm_103__regCR0,
  Convert__imm_103__RegCRRC1_0,
  Convert__imm_102__regCR0,
  Convert__imm_102__RegCRRC1_0,
  Convert__imm_108__regCR0__CondBr1_0,
  Convert__imm_108__RegCRRC1_0__CondBr1_1,
  Convert__imm_111__regCR0__CondBr1_0,
  Convert__imm_111__RegCRRC1_0__CondBr1_1,
  Convert__imm_110__regCR0__CondBr1_0,
  Convert__imm_110__RegCRRC1_0__CondBr1_1,
  Convert__imm_108__regCR0,
  Convert__imm_108__RegCRRC1_0,
  Convert__imm_111__regCR0,
  Convert__imm_111__RegCRRC1_0,
  Convert__imm_110__regCR0,
  Convert__imm_110__RegCRRC1_0,
  Convert__imm_12__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_15__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_14__RegCRBITRC1_0__CondBr1_1,
  Convert__imm_12__RegCRBITRC1_0__imm_0,
  Convert__imm_15__RegCRBITRC1_0__imm_0,
  Convert__imm_14__RegCRBITRC1_0__imm_0,
  Convert__RegG8RC1_0__RegG8RC1_1__imm_0__U6Imm1_2,
  Convert__RegG8RC1_1__RegG8RC1_2__imm_0__U6Imm1_3,
  Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3,
  Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4,
  Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3,
  Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4,
  Convert__RegGPRC1_0__RegGPRC1_1__imm_0__U5Imm1_2__imm_31,
  Convert__RegGPRC1_1__RegGPRC1_2__imm_0__U5Imm1_3__imm_31,
  Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2,
  Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3,
  Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2,
  Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3,
  Convert__RegCRRC1_0__RegGPRC1_2__RegGPRC1_3,
  Convert__RegCRRC1_0__RegG8RC1_2__RegG8RC1_3,
  Convert__regCR0__RegG8RC1_0__RegG8RC1_1,
  Convert__RegCRRC1_0__RegG8RC1_1__RegG8RC1_2,
  Convert__regCR0__RegG8RC1_0__S16Imm1_1,
  Convert__RegCRRC1_0__RegG8RC1_1__S16Imm1_2,
  Convert__RegCRRC1_0__RegGPRC1_2__S16Imm1_3,
  Convert__RegCRRC1_0__RegG8RC1_2__S16Imm1_3,
  Convert__regCR0__RegG8RC1_0__U16Imm1_1,
  Convert__RegCRRC1_0__RegG8RC1_1__U16Imm1_2,
  Convert__RegCRRC1_0__RegGPRC1_2__U16Imm1_3,
  Convert__RegCRRC1_0__RegG8RC1_2__U16Imm1_3,
  Convert__regCR0__RegGPRC1_0__RegGPRC1_1,
  Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2,
  Convert__regCR0__RegGPRC1_0__U16Imm1_1,
  Convert__RegCRRC1_0__RegGPRC1_1__U16Imm1_2,
  Convert__regCR0__RegGPRC1_0__S16Imm1_1,
  Convert__RegCRRC1_0__RegGPRC1_1__S16Imm1_2,
  Convert__RegG8RC1_0__RegG8RC1_1,
  Convert__RegG8RC1_1__RegG8RC1_2,
  Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2,
  Convert__RegCRBITRC1_0__RegCRBITRC1_0__RegCRBITRC1_0,
  Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_1,
  Convert__RegGxRCNoR01_0__RegGxRC1_1,
  Convert__regR0__regR0,
  Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2,
  Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3,
  Convert__U5Imm1_0,
  Convert__U5Imm1_2__RegGPRC1_0__RegGPRC1_1,
  Convert__RegGPRC1_0__RegGPRC1_2__U5Imm1_1,
  Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2,
  Convert__RegGPRC1_0__DispSPE21_1__RegGxRCNoR01_2,
  Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2,
  Convert__RegGPRC1_0__Imm1_1,
  Convert__RegGPRC1_0__U5Imm1_1__RegGPRC1_2,
  Convert__RegF4RC1_0__RegF4RC1_1,
  Convert__RegF4RC1_1__RegF4RC1_2,
  Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2,
  Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3,
  Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2,
  Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3,
  Convert__RegF8RC1_0__RegF8RC1_1,
  Convert__RegF8RC1_1__RegF8RC1_2,
  Convert__RegF4RC1_0__RegF8RC1_1,
  Convert__RegF4RC1_1__RegF8RC1_2,
  Convert__RegCRRC1_0__RegF4RC1_1__RegF4RC1_2,
  Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3,
  Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3__RegF8RC1_4,
  Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3,
  Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3__RegF4RC1_4,
  Convert__RegF4RC1_0__RegF8RC1_1__RegF4RC1_2__RegF4RC1_3,
  Convert__RegF4RC1_1__RegF8RC1_2__RegF4RC1_3__RegF4RC1_4,
  Convert__U4Imm1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegGPRC1_0__RegGPRCNoR01_1__RegGPRC1_2__RegCRBITRC1_3,
  Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__RegGPRC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__RegGPRC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2,
  Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegG8RC1_0__imm_0__DispRIX1_1__RegGxRCNoR01_2,
  Convert__RegG8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__RegF8RC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__RegF8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__RegF4RC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__RegF4RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegGPRC1_0__S16Imm1_1,
  Convert__RegGPRC1_0__S17Imm1_1,
  Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__imm_1,
  Convert__RegVSFRC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__imm_0,
  Convert__RegCRRC1_0__RegCRRC1_1,
  Convert__RegGPRC1_0__imm_29,
  Convert__RegGPRC1_0__imm_280,
  Convert__RegGPRC1_0__imm_128,
  Convert__RegGPRC1_0__imm_129,
  Convert__RegGPRC1_0__imm_130,
  Convert__RegGPRC1_0__imm_131,
  Convert__RegGPRC1_0__imm_132,
  Convert__RegGPRC1_0__imm_133,
  Convert__RegGPRC1_0__imm_134,
  Convert__RegGPRC1_0__imm_135,
  Convert__RegGPRC1_0__imm_28,
  Convert__RegGPRC1_0,
  Convert__RegGPRC1_0__imm_19,
  Convert__RegGPRC1_0__imm_537,
  Convert__RegGPRC1_0__imm_539,
  Convert__RegGPRC1_0__imm_541,
  Convert__RegGPRC1_0__imm_543,
  Convert__RegGPRC1_0__imm_536,
  Convert__RegGPRC1_0__imm_538,
  Convert__RegGPRC1_0__imm_540,
  Convert__RegGPRC1_0__imm_542,
  Convert__RegGPRC1_0__imm_1018,
  Convert__RegGPRC1_0__imm_981,
  Convert__RegGPRC1_0__imm_22,
  Convert__RegGPRC1_0__imm_17,
  Convert__RegGPRC1_0__imm_18,
  Convert__RegGPRC1_0__imm_980,
  Convert__RegF8RC1_0,
  Convert__RegGPRC1_0__imm_529,
  Convert__RegGPRC1_0__imm_531,
  Convert__RegGPRC1_0__imm_533,
  Convert__RegGPRC1_0__imm_535,
  Convert__RegGPRC1_0__imm_528,
  Convert__RegGPRC1_0__imm_530,
  Convert__RegGPRC1_0__imm_532,
  Convert__RegGPRC1_0__imm_534,
  Convert__RegGPRC1_0__imm_1019,
  Convert__RegGPRC1_0__CRBitMask1_1,
  Convert__RegGPRC1_0__imm_48,
  Convert__RegGPRC1_0__imm_287,
  Convert__RegGPRC1_0__imm_5,
  Convert__RegGPRC1_0__imm_4,
  Convert__RegGPRC1_0__imm_25,
  Convert__RegGPRC1_0__imm_512,
  Convert__RegGPRC1_0__imm_272,
  Convert__RegGPRC1_0__imm_273,
  Convert__RegGPRC1_0__imm_274,
  Convert__RegGPRC1_0__imm_275,
  Convert__RegGPRC1_0__imm_260,
  Convert__RegGPRC1_0__imm_261,
  Convert__RegGPRC1_0__imm_262,
  Convert__RegGPRC1_0__imm_263,
  Convert__RegGPRC1_0__U4Imm1_1,
  Convert__RegGPRC1_0__imm_26,
  Convert__RegGPRC1_0__imm_27,
  Convert__RegGPRC1_0__imm_990,
  Convert__RegGPRC1_0__imm_991,
  Convert__RegGPRC1_0__imm_268,
  Convert__RegGPRC1_0__imm_988,
  Convert__RegGPRC1_0__imm_989,
  Convert__RegGPRC1_0__imm_269,
  Convert__RegGPRC1_0__imm_986,
  Convert__RegVRRC1_0,
  Convert__RegGPRC1_0__imm_1,
  Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_1,
  Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_2,
  Convert__imm_29__RegGPRC1_0,
  Convert__imm_280__RegGPRC1_0,
  Convert__imm_28__RegGPRC1_0,
  Convert__imm_255__RegG8RC1_0,
  Convert__Imm1_0__RegGPRC1_1,
  Convert__imm_19__RegGPRC1_0,
  Convert__imm_537__RegGPRC1_1,
  Convert__imm_539__RegGPRC1_1,
  Convert__imm_541__RegGPRC1_1,
  Convert__imm_543__RegGPRC1_1,
  Convert__imm_536__RegGPRC1_1,
  Convert__imm_538__RegGPRC1_1,
  Convert__imm_540__RegGPRC1_1,
  Convert__imm_542__RegGPRC1_1,
  Convert__imm_1018__RegGPRC1_0,
  Convert__RegGPRC1_1__Imm1_0,
  Convert__imm_981__RegGPRC1_0,
  Convert__imm_22__RegGPRC1_0,
  Convert__imm_17__RegGPRC1_0,
  Convert__imm_18__RegGPRC1_0,
  Convert__imm_980__RegGPRC1_0,
  Convert__Imm1_0__RegF8RC1_1,
  Convert__imm_529__RegGPRC1_1,
  Convert__imm_531__RegGPRC1_1,
  Convert__imm_533__RegGPRC1_1,
  Convert__imm_535__RegGPRC1_1,
  Convert__imm_528__RegGPRC1_1,
  Convert__imm_530__RegGPRC1_1,
  Convert__imm_532__RegGPRC1_1,
  Convert__imm_534__RegGPRC1_1,
  Convert__imm_1019__RegGPRC1_0,
  Convert__RegGPRC1_0__imm_0,
  Convert__CRBitMask1_0__RegGPRC1_1,
  Convert__imm_48__RegGPRC1_0,
  Convert__imm_25__RegGPRC1_0,
  Convert__imm_512__RegGPRC1_0,
  Convert__imm_272__RegGPRC1_1,
  Convert__imm_273__RegGPRC1_1,
  Convert__imm_274__RegGPRC1_1,
  Convert__imm_275__RegGPRC1_1,
  Convert__imm_260__RegGPRC1_1,
  Convert__imm_261__RegGPRC1_1,
  Convert__imm_262__RegGPRC1_1,
  Convert__imm_263__RegGPRC1_1,
  Convert__imm_272__RegGPRC1_0,
  Convert__imm_273__RegGPRC1_0,
  Convert__imm_274__RegGPRC1_0,
  Convert__imm_275__RegGPRC1_0,
  Convert__imm_260__RegGPRC1_0,
  Convert__imm_261__RegGPRC1_0,
  Convert__imm_262__RegGPRC1_0,
  Convert__imm_263__RegGPRC1_0,
  Convert__RegGPRC1_1__U4Imm1_0,
  Convert__imm_26__RegGPRC1_0,
  Convert__imm_27__RegGPRC1_0,
  Convert__imm_990__RegGPRC1_0,
  Convert__imm_991__RegGPRC1_0,
  Convert__imm_988__RegGPRC1_0,
  Convert__imm_284__RegGPRC1_0,
  Convert__imm_989__RegGPRC1_0,
  Convert__imm_285__RegGPRC1_0,
  Convert__imm_986__RegGPRC1_0,
  Convert__imm_1__RegGPRC1_0,
  Convert__RegGPRC1_0__RegGPRC1_1__U16Imm1_2,
  Convert__imm_2,
  Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__U6Imm1_3,
  Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__U6Imm1_4,
  Convert__RegG8RC1_0__Tie0__RegG8RC1_1__U6Imm1_2__U6Imm1_3,
  Convert__RegG8RC1_1__Tie0__RegG8RC1_2__U6Imm1_3__U6Imm1_4,
  Convert__RegGPRC1_0__Tie0__RegGPRC1_1__U5Imm1_2__U5Imm1_3__U5Imm1_4,
  Convert__RegGPRC1_1__Tie0__RegGPRC1_2__U5Imm1_3__U5Imm1_4__U5Imm1_5,
  Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3__U5Imm1_4,
  Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4__U5Imm1_5,
  Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4,
  Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3__U5Imm1_4__U5Imm1_5,
  Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__imm_0,
  Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__imm_0,
  Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__imm_0,
  Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__imm_0,
  Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2__imm_0__imm_31,
  Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3__imm_0__imm_31,
  Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__imm_0__imm_31,
  Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__imm_0__imm_31,
  Convert__Imm1_0,
  Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2,
  Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3,
  Convert__imm_0__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__imm_0__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegG8RC1_1__RegGxRCNoR01_2__RegGxRC1_3,
  Convert__imm_0__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2,
  Convert__imm_0__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__imm_0__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__imm_0__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__imm_0__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2,
  Convert__imm_0__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2,
  Convert__RegGPRC1_1__RegGxRCNoR01_2__RegGxRC1_3,
  Convert__RegG8RC1_0__RegG8RC1_2__RegG8RC1_1,
  Convert__RegG8RC1_1__RegG8RC1_3__RegG8RC1_2,
  Convert__U5Imm1_0__RegG8RC1_1__RegG8RC1_2,
  Convert__imm_4__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_4__RegG8RC1_0__S16Imm1_1,
  Convert__imm_12__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_12__RegG8RC1_0__S16Imm1_1,
  Convert__imm_8__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_8__RegG8RC1_0__S16Imm1_1,
  Convert__U5Imm1_0__RegG8RC1_1__S16Imm1_2,
  Convert__imm_20__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_20__RegG8RC1_0__S16Imm1_1,
  Convert__imm_5__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_5__RegG8RC1_0__S16Imm1_1,
  Convert__imm_1__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_1__RegG8RC1_0__S16Imm1_1,
  Convert__imm_6__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_6__RegG8RC1_0__S16Imm1_1,
  Convert__imm_2__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_2__RegG8RC1_0__S16Imm1_1,
  Convert__imm_16__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_16__RegG8RC1_0__S16Imm1_1,
  Convert__imm_24__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_24__RegG8RC1_0__S16Imm1_1,
  Convert__imm_31__RegG8RC1_0__RegG8RC1_1,
  Convert__imm_31__RegG8RC1_0__S16Imm1_1,
  Convert__regR0__RegGPRC1_0,
  Convert__RegGPRC1_1__RegGPRC1_0,
  Convert__RegGPRC1_0__RegGPRC1_1__Imm1_2,
  Convert__RegGPRC1_0__RegGPRC1_1__imm_0,
  Convert__RegGPRC1_0__RegGPRC1_1__imm_1,
  Convert__U5Imm1_0__RegGPRC1_1__RegGPRC1_2,
  Convert__imm_4__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_4__RegGPRC1_0__S16Imm1_1,
  Convert__imm_12__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_12__RegGPRC1_0__S16Imm1_1,
  Convert__imm_8__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_8__RegGPRC1_0__S16Imm1_1,
  Convert__U5Imm1_0__RegGPRC1_1__S16Imm1_2,
  Convert__imm_20__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_20__RegGPRC1_0__S16Imm1_1,
  Convert__imm_5__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_5__RegGPRC1_0__S16Imm1_1,
  Convert__imm_1__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_1__RegGPRC1_0__S16Imm1_1,
  Convert__imm_6__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_6__RegGPRC1_0__S16Imm1_1,
  Convert__imm_2__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_2__RegGPRC1_0__S16Imm1_1,
  Convert__imm_16__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_16__RegGPRC1_0__S16Imm1_1,
  Convert__imm_24__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_24__RegGPRC1_0__S16Imm1_1,
  Convert__imm_31__RegGPRC1_0__RegGPRC1_1,
  Convert__imm_31__RegGPRC1_0__S16Imm1_1,
  Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2,
  Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1,
  Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3,
  Convert__RegVRRC1_0__RegVRRC1_1,
  Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3,
  Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__U5Imm1_3,
  Convert__RegVRRC1_0__S5Imm1_1,
  Convert__regR0__regR0__imm_0,
  Convert__RegVSFRC1_0__RegVSFRC1_1,
  Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2,
  Convert__RegCRRC1_0__RegVSFRC1_1__RegVSFRC1_2,
  Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2,
  Convert__RegCRRC1_0__RegVSFRC1_1,
  Convert__RegVSRC1_0__RegVSRC1_1,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2,
  Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3,
  Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1,
  Convert__RegCRRC1_0__RegVSRC1_1__RegVSRC1_2,
  Convert__RegCRRC1_0__RegVSRC1_1,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__imm_0,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__imm_3,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__U2Imm1_3,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_0,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_3,
  Convert__RegVSRC1_0__RegVSRC1_1__U2Imm1_2,
  Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_2,
  CVT_NUM_SIGNATURES
};

} // end anonymous namespace

static const uint8_t ConversionTable[CVT_NUM_SIGNATURES][13] = {
  // Convert__RegG8RC1_0__RegG8RC1_1__TLSReg1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addTLSRegOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRCNoR01_1__S16Imm1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCNoR0Operands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__S16Imm1_3
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addS16ImmOperands, 4, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRCNoR01_1__S17Imm1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCNoR0Operands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__U16Imm1_3
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addU16ImmOperands, 4, CVT_Done },
  // Convert_NoOperands
  { CVT_Done },
  // Convert__DirectBr1_0
  { CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__U5Imm1_0__RegCRBITRC1_1__CondBr1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegCRBITRCOperands, 2, CVT_95_addBranchTargetOperands, 3, CVT_Done },
  // Convert__U5Imm1_0__RegCRBITRC1_1__imm_0
  { CVT_95_addImmOperands, 1, CVT_95_addRegCRBITRCOperands, 2, CVT_imm_0, 0, CVT_Done },
  // Convert__U5Imm1_0__RegCRBITRC1_1__Imm1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegCRBITRCOperands, 2, CVT_95_addImmOperands, 3, CVT_Done },
  // Convert__CondBr1_0
  { CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_0__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_0, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_0__RegCRBITRC1_0__imm_0
  { CVT_imm_0, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_8__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_8, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_8__RegCRBITRC1_0__imm_0
  { CVT_imm_8, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_2__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_2, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_2__RegCRBITRC1_0__imm_0
  { CVT_imm_2, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_10__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_10, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_10__RegCRBITRC1_0__imm_0
  { CVT_imm_10, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_76__regCR0__CondBr1_0
  { CVT_imm_76, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_76__RegCRRC1_0__CondBr1_1
  { CVT_imm_76, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_79__regCR0__CondBr1_0
  { CVT_imm_79, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_79__RegCRRC1_0__CondBr1_1
  { CVT_imm_79, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_78__regCR0__CondBr1_0
  { CVT_imm_78, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_78__RegCRRC1_0__CondBr1_1
  { CVT_imm_78, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_76__regCR0
  { CVT_imm_76, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_76__RegCRRC1_0
  { CVT_imm_76, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_79__regCR0
  { CVT_imm_79, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_79__RegCRRC1_0
  { CVT_imm_79, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_78__regCR0
  { CVT_imm_78, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_78__RegCRRC1_0
  { CVT_imm_78, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_4__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_4, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_7__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_7, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_6__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_6, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_4__RegCRBITRC1_0__imm_0
  { CVT_imm_4, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_7__RegCRBITRC1_0__imm_0
  { CVT_imm_7, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_6__RegCRBITRC1_0__imm_0
  { CVT_imm_6, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_4__regCR0__CondBr1_0
  { CVT_imm_4, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_4__RegCRRC1_0__CondBr1_1
  { CVT_imm_4, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_7__regCR0__CondBr1_0
  { CVT_imm_7, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_7__RegCRRC1_0__CondBr1_1
  { CVT_imm_7, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_6__regCR0__CondBr1_0
  { CVT_imm_6, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_6__RegCRRC1_0__CondBr1_1
  { CVT_imm_6, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_4__regCR0
  { CVT_imm_4, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_4__RegCRRC1_0
  { CVT_imm_4, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_7__regCR0
  { CVT_imm_7, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_7__RegCRRC1_0
  { CVT_imm_7, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_6__regCR0
  { CVT_imm_6, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_6__RegCRRC1_0
  { CVT_imm_6, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_44__regCR0__CondBr1_0
  { CVT_imm_44, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_44__RegCRRC1_0__CondBr1_1
  { CVT_imm_44, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_47__regCR0__CondBr1_0
  { CVT_imm_47, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_47__RegCRRC1_0__CondBr1_1
  { CVT_imm_47, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_46__regCR0__CondBr1_0
  { CVT_imm_46, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_46__RegCRRC1_0__CondBr1_1
  { CVT_imm_46, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_44__regCR0
  { CVT_imm_44, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_44__RegCRRC1_0
  { CVT_imm_44, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_47__regCR0
  { CVT_imm_47, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_47__RegCRRC1_0
  { CVT_imm_47, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_46__regCR0
  { CVT_imm_46, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_46__RegCRRC1_0
  { CVT_imm_46, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__DirectBr1_0__Imm1_1
  { CVT_95_addBranchTargetOperands, 1, CVT_95_addImmOperands, 2, CVT_Done },
  // Convert__imm_36__regCR0__CondBr1_0
  { CVT_imm_36, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_36__RegCRRC1_0__CondBr1_1
  { CVT_imm_36, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_39__regCR0__CondBr1_0
  { CVT_imm_39, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_39__RegCRRC1_0__CondBr1_1
  { CVT_imm_39, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_38__regCR0__CondBr1_0
  { CVT_imm_38, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_38__RegCRRC1_0__CondBr1_1
  { CVT_imm_38, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_36__regCR0
  { CVT_imm_36, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_36__RegCRRC1_0
  { CVT_imm_36, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_39__regCR0
  { CVT_imm_39, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_39__RegCRRC1_0
  { CVT_imm_39, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_38__regCR0
  { CVT_imm_38, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_38__RegCRRC1_0
  { CVT_imm_38, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_12__regCR0__CondBr1_0
  { CVT_imm_12, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_12__RegCRRC1_0__CondBr1_1
  { CVT_imm_12, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_15__regCR0__CondBr1_0
  { CVT_imm_15, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_15__RegCRRC1_0__CondBr1_1
  { CVT_imm_15, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_14__regCR0__CondBr1_0
  { CVT_imm_14, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_14__RegCRRC1_0__CondBr1_1
  { CVT_imm_14, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_12__regCR0
  { CVT_imm_12, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_12__RegCRRC1_0
  { CVT_imm_12, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_15__regCR0
  { CVT_imm_15, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_15__RegCRRC1_0
  { CVT_imm_15, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_14__regCR0
  { CVT_imm_14, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_14__RegCRRC1_0
  { CVT_imm_14, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_68__regCR0__CondBr1_0
  { CVT_imm_68, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_68__RegCRRC1_0__CondBr1_1
  { CVT_imm_68, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_71__regCR0__CondBr1_0
  { CVT_imm_71, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_71__RegCRRC1_0__CondBr1_1
  { CVT_imm_71, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_70__regCR0__CondBr1_0
  { CVT_imm_70, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_70__RegCRRC1_0__CondBr1_1
  { CVT_imm_70, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_68__regCR0
  { CVT_imm_68, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_68__RegCRRC1_0
  { CVT_imm_68, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_71__regCR0
  { CVT_imm_71, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_71__RegCRRC1_0
  { CVT_imm_71, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_70__regCR0
  { CVT_imm_70, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_70__RegCRRC1_0
  { CVT_imm_70, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_100__regCR0__CondBr1_0
  { CVT_imm_100, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_100__RegCRRC1_0__CondBr1_1
  { CVT_imm_100, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_103__regCR0__CondBr1_0
  { CVT_imm_103, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_103__RegCRRC1_0__CondBr1_1
  { CVT_imm_103, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_102__regCR0__CondBr1_0
  { CVT_imm_102, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_102__RegCRRC1_0__CondBr1_1
  { CVT_imm_102, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_100__regCR0
  { CVT_imm_100, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_100__RegCRRC1_0
  { CVT_imm_100, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_103__regCR0
  { CVT_imm_103, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_103__RegCRRC1_0
  { CVT_imm_103, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_102__regCR0
  { CVT_imm_102, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_102__RegCRRC1_0
  { CVT_imm_102, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_108__regCR0__CondBr1_0
  { CVT_imm_108, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_108__RegCRRC1_0__CondBr1_1
  { CVT_imm_108, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_111__regCR0__CondBr1_0
  { CVT_imm_111, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_111__RegCRRC1_0__CondBr1_1
  { CVT_imm_111, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_110__regCR0__CondBr1_0
  { CVT_imm_110, 0, CVT_regCR0, 0, CVT_95_addBranchTargetOperands, 1, CVT_Done },
  // Convert__imm_110__RegCRRC1_0__CondBr1_1
  { CVT_imm_110, 0, CVT_95_addRegCRRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_108__regCR0
  { CVT_imm_108, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_108__RegCRRC1_0
  { CVT_imm_108, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_111__regCR0
  { CVT_imm_111, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_111__RegCRRC1_0
  { CVT_imm_111, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_110__regCR0
  { CVT_imm_110, 0, CVT_regCR0, 0, CVT_Done },
  // Convert__imm_110__RegCRRC1_0
  { CVT_imm_110, 0, CVT_95_addRegCRRCOperands, 1, CVT_Done },
  // Convert__imm_12__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_12, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_15__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_15, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_14__RegCRBITRC1_0__CondBr1_1
  { CVT_imm_14, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addBranchTargetOperands, 2, CVT_Done },
  // Convert__imm_12__RegCRBITRC1_0__imm_0
  { CVT_imm_12, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_15__RegCRBITRC1_0__imm_0
  { CVT_imm_15, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__imm_14__RegCRBITRC1_0__imm_0
  { CVT_imm_14, 0, CVT_95_addRegCRBITRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__imm_0__U6Imm1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_imm_0, 0, CVT_95_addImmOperands, 3, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__imm_0__U6Imm1_3
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_imm_0, 0, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addImmOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__imm_0__U5Imm1_2__imm_31
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_imm_0, 0, CVT_95_addImmOperands, 3, CVT_imm_31, 0, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__imm_0__U5Imm1_3__imm_31
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_imm_0, 0, CVT_95_addImmOperands, 4, CVT_imm_31, 0, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addImmOperands, 3, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 3, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegCRRC1_0__RegGPRC1_2__RegGPRC1_3
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegGPRCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_Done },
  // Convert__RegCRRC1_0__RegG8RC1_2__RegG8RC1_3
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegG8RCOperands, 4, CVT_Done },
  // Convert__regCR0__RegG8RC1_0__RegG8RC1_1
  { CVT_regCR0, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegG8RC1_1__RegG8RC1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_Done },
  // Convert__regCR0__RegG8RC1_0__S16Imm1_1
  { CVT_regCR0, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegG8RC1_1__S16Imm1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__RegCRRC1_0__RegGPRC1_2__S16Imm1_3
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegGPRCOperands, 3, CVT_95_addS16ImmOperands, 4, CVT_Done },
  // Convert__RegCRRC1_0__RegG8RC1_2__S16Imm1_3
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegG8RCOperands, 3, CVT_95_addS16ImmOperands, 4, CVT_Done },
  // Convert__regCR0__RegG8RC1_0__U16Imm1_1
  { CVT_regCR0, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addU16ImmOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegG8RC1_1__U16Imm1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addU16ImmOperands, 3, CVT_Done },
  // Convert__RegCRRC1_0__RegGPRC1_2__U16Imm1_3
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegGPRCOperands, 3, CVT_95_addU16ImmOperands, 4, CVT_Done },
  // Convert__RegCRRC1_0__RegG8RC1_2__U16Imm1_3
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegG8RCOperands, 3, CVT_95_addU16ImmOperands, 4, CVT_Done },
  // Convert__regCR0__RegGPRC1_0__RegGPRC1_1
  { CVT_regCR0, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_Done },
  // Convert__regCR0__RegGPRC1_0__U16Imm1_1
  { CVT_regCR0, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addU16ImmOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegGPRC1_1__U16Imm1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addU16ImmOperands, 3, CVT_Done },
  // Convert__regCR0__RegGPRC1_0__S16Imm1_1
  { CVT_regCR0, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegGPRC1_1__S16Imm1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_Done },
  // Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2
  { CVT_95_addRegCRBITRCOperands, 1, CVT_95_addRegCRBITRCOperands, 2, CVT_95_addRegCRBITRCOperands, 3, CVT_Done },
  // Convert__RegCRBITRC1_0__RegCRBITRC1_0__RegCRBITRC1_0
  { CVT_95_addRegCRBITRCOperands, 1, CVT_95_addRegCRBITRCOperands, 1, CVT_95_addRegCRBITRCOperands, 1, CVT_Done },
  // Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_1
  { CVT_95_addRegCRBITRCOperands, 1, CVT_95_addRegCRBITRCOperands, 2, CVT_95_addRegCRBITRCOperands, 2, CVT_Done },
  // Convert__RegGxRCNoR01_0__RegGxRC1_1
  { CVT_95_addRegGxRCNoR0Operands, 1, CVT_95_addRegGxRCOperands, 2, CVT_Done },
  // Convert__regR0__regR0
  { CVT_regR0, 0, CVT_regR0, 0, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegG8RCOperands, 4, CVT_Done },
  // Convert__U5Imm1_0
  { CVT_95_addImmOperands, 1, CVT_Done },
  // Convert__U5Imm1_2__RegGPRC1_0__RegGPRC1_1
  { CVT_95_addImmOperands, 3, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_2__U5Imm1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegGPRC1_0__DispSPE21_1__RegGxRCNoR01_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegGPRC1_0__Imm1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addImmOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__U5Imm1_1__RegGPRC1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addImmOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_Done },
  // Convert__RegF4RC1_0__RegF4RC1_1
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addRegF4RCOperands, 2, CVT_Done },
  // Convert__RegF4RC1_1__RegF4RC1_2
  { CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_Done },
  // Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2
  { CVT_95_addRegF8RCOperands, 1, CVT_95_addRegF8RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_Done },
  // Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3
  { CVT_95_addRegF8RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_95_addRegF8RCOperands, 4, CVT_Done },
  // Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_Done },
  // Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3
  { CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_95_addRegF4RCOperands, 4, CVT_Done },
  // Convert__RegF8RC1_0__RegF8RC1_1
  { CVT_95_addRegF8RCOperands, 1, CVT_95_addRegF8RCOperands, 2, CVT_Done },
  // Convert__RegF8RC1_1__RegF8RC1_2
  { CVT_95_addRegF8RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_Done },
  // Convert__RegF4RC1_0__RegF8RC1_1
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addRegF8RCOperands, 2, CVT_Done },
  // Convert__RegF4RC1_1__RegF8RC1_2
  { CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_Done },
  // Convert__RegCRRC1_0__RegF4RC1_1__RegF4RC1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_Done },
  // Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3
  { CVT_95_addRegF8RCOperands, 1, CVT_95_addRegF8RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_95_addRegF8RCOperands, 4, CVT_Done },
  // Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3__RegF8RC1_4
  { CVT_95_addRegF8RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_95_addRegF8RCOperands, 4, CVT_95_addRegF8RCOperands, 5, CVT_Done },
  // Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_95_addRegF4RCOperands, 4, CVT_Done },
  // Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3__RegF4RC1_4
  { CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_95_addRegF4RCOperands, 4, CVT_95_addRegF4RCOperands, 5, CVT_Done },
  // Convert__RegF4RC1_0__RegF8RC1_1__RegF4RC1_2__RegF4RC1_3
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addRegF8RCOperands, 2, CVT_95_addRegF4RCOperands, 3, CVT_95_addRegF4RCOperands, 4, CVT_Done },
  // Convert__RegF4RC1_1__RegF8RC1_2__RegF4RC1_3__RegF4RC1_4
  { CVT_95_addRegF4RCOperands, 2, CVT_95_addRegF8RCOperands, 3, CVT_95_addRegF4RCOperands, 4, CVT_95_addRegF4RCOperands, 5, CVT_Done },
  // Convert__U4Imm1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRCNoR01_1__RegGPRC1_2__RegCRBITRC1_3
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCNoR0Operands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addRegCRBITRCOperands, 4, CVT_Done },
  // Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegGPRC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_0, 0, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegGPRC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_0, 0, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegG8RC1_0__imm_0__DispRIX1_1__RegGxRCNoR01_2
  { CVT_95_addRegG8RCOperands, 1, CVT_imm_0, 0, CVT_95_addImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegG8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_imm_0, 0, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_95_addRegF8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegF8RC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_95_addRegF8RCOperands, 1, CVT_imm_0, 0, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegF8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegF8RCOperands, 1, CVT_imm_0, 0, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegF8RCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegF4RC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_95_addRegF4RCOperands, 1, CVT_imm_0, 0, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__RegF4RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegF4RCOperands, 1, CVT_imm_0, 0, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegF4RCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__S16Imm1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__S17Imm1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__imm_1
  { CVT_imm_1, 0, CVT_Done },
  // Convert__RegVSFRC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegVSFRCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__imm_0
  { CVT_imm_0, 0, CVT_Done },
  // Convert__RegCRRC1_0__RegCRRC1_1
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegCRRCOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__imm_29
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_29, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_280
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_280, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_128
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_128, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_129
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_129, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_130
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_130, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_131
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_131, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_132
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_132, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_133
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_133, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_134
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_134, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_135
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_135, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_28
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_28, 0, CVT_Done },
  // Convert__RegGPRC1_0
  { CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_0__imm_19
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_19, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_537
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_537, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_539
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_539, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_541
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_541, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_543
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_543, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_536
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_536, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_538
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_538, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_540
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_540, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_542
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_542, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_1018
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_1018, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_981
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_981, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_22
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_22, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_17
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_17, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_18
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_18, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_980
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_980, 0, CVT_Done },
  // Convert__RegF8RC1_0
  { CVT_95_addRegF8RCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_0__imm_529
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_529, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_531
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_531, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_533
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_533, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_535
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_535, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_528
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_528, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_530
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_530, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_532
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_532, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_534
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_534, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_1019
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_1019, 0, CVT_Done },
  // Convert__RegGPRC1_0__CRBitMask1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addCRBitMaskOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__imm_48
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_48, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_287
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_287, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_5
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_5, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_4
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_4, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_25
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_25, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_512
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_512, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_272
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_272, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_273
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_273, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_274
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_274, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_275
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_275, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_260
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_260, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_261
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_261, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_262
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_262, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_263
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_263, 0, CVT_Done },
  // Convert__RegGPRC1_0__U4Imm1_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addImmOperands, 2, CVT_Done },
  // Convert__RegGPRC1_0__imm_26
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_26, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_27
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_27, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_990
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_990, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_991
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_991, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_268
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_268, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_988
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_988, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_989
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_989, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_269
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_269, 0, CVT_Done },
  // Convert__RegGPRC1_0__imm_986
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_986, 0, CVT_Done },
  // Convert__RegVRRC1_0
  { CVT_95_addRegVRRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_0__imm_1
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_1, 0, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_1
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_2
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegG8RCOperands, 3, CVT_Done },
  // Convert__imm_29__RegGPRC1_0
  { CVT_imm_29, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_280__RegGPRC1_0
  { CVT_imm_280, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_28__RegGPRC1_0
  { CVT_imm_28, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_255__RegG8RC1_0
  { CVT_imm_255, 0, CVT_95_addRegG8RCOperands, 1, CVT_Done },
  // Convert__Imm1_0__RegGPRC1_1
  { CVT_95_addImmOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_19__RegGPRC1_0
  { CVT_imm_19, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_537__RegGPRC1_1
  { CVT_imm_537, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_539__RegGPRC1_1
  { CVT_imm_539, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_541__RegGPRC1_1
  { CVT_imm_541, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_543__RegGPRC1_1
  { CVT_imm_543, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_536__RegGPRC1_1
  { CVT_imm_536, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_538__RegGPRC1_1
  { CVT_imm_538, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_540__RegGPRC1_1
  { CVT_imm_540, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_542__RegGPRC1_1
  { CVT_imm_542, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_1018__RegGPRC1_0
  { CVT_imm_1018, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_1__Imm1_0
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 1, CVT_Done },
  // Convert__imm_981__RegGPRC1_0
  { CVT_imm_981, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_22__RegGPRC1_0
  { CVT_imm_22, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_17__RegGPRC1_0
  { CVT_imm_17, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_18__RegGPRC1_0
  { CVT_imm_18, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_980__RegGPRC1_0
  { CVT_imm_980, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__Imm1_0__RegF8RC1_1
  { CVT_95_addImmOperands, 1, CVT_95_addRegF8RCOperands, 2, CVT_Done },
  // Convert__imm_529__RegGPRC1_1
  { CVT_imm_529, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_531__RegGPRC1_1
  { CVT_imm_531, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_533__RegGPRC1_1
  { CVT_imm_533, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_535__RegGPRC1_1
  { CVT_imm_535, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_528__RegGPRC1_1
  { CVT_imm_528, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_530__RegGPRC1_1
  { CVT_imm_530, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_532__RegGPRC1_1
  { CVT_imm_532, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_534__RegGPRC1_1
  { CVT_imm_534, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_1019__RegGPRC1_0
  { CVT_imm_1019, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_0__imm_0
  { CVT_95_addRegGPRCOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__CRBitMask1_0__RegGPRC1_1
  { CVT_95_addCRBitMaskOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_48__RegGPRC1_0
  { CVT_imm_48, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_25__RegGPRC1_0
  { CVT_imm_25, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_512__RegGPRC1_0
  { CVT_imm_512, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_272__RegGPRC1_1
  { CVT_imm_272, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_273__RegGPRC1_1
  { CVT_imm_273, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_274__RegGPRC1_1
  { CVT_imm_274, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_275__RegGPRC1_1
  { CVT_imm_275, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_260__RegGPRC1_1
  { CVT_imm_260, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_261__RegGPRC1_1
  { CVT_imm_261, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_262__RegGPRC1_1
  { CVT_imm_262, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_263__RegGPRC1_1
  { CVT_imm_263, 0, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_272__RegGPRC1_0
  { CVT_imm_272, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_273__RegGPRC1_0
  { CVT_imm_273, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_274__RegGPRC1_0
  { CVT_imm_274, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_275__RegGPRC1_0
  { CVT_imm_275, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_260__RegGPRC1_0
  { CVT_imm_260, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_261__RegGPRC1_0
  { CVT_imm_261, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_262__RegGPRC1_0
  { CVT_imm_262, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_263__RegGPRC1_0
  { CVT_imm_263, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_1__U4Imm1_0
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 1, CVT_Done },
  // Convert__imm_26__RegGPRC1_0
  { CVT_imm_26, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_27__RegGPRC1_0
  { CVT_imm_27, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_990__RegGPRC1_0
  { CVT_imm_990, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_991__RegGPRC1_0
  { CVT_imm_991, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_988__RegGPRC1_0
  { CVT_imm_988, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_284__RegGPRC1_0
  { CVT_imm_284, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_989__RegGPRC1_0
  { CVT_imm_989, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_285__RegGPRC1_0
  { CVT_imm_285, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_986__RegGPRC1_0
  { CVT_imm_986, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__imm_1__RegGPRC1_0
  { CVT_imm_1, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__U16Imm1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addU16ImmOperands, 3, CVT_Done },
  // Convert__imm_2
  { CVT_imm_2, 0, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__U6Imm1_3
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__U6Imm1_4
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegG8RC1_0__Tie0__RegG8RC1_1__U6Imm1_2__U6Imm1_3
  { CVT_95_addRegG8RCOperands, 1, CVT_Tied, 0, CVT_95_addRegG8RCOperands, 2, CVT_95_addImmOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegG8RC1_1__Tie0__RegG8RC1_2__U6Imm1_3__U6Imm1_4
  { CVT_95_addRegG8RCOperands, 2, CVT_Tied, 0, CVT_95_addRegG8RCOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegGPRC1_0__Tie0__RegGPRC1_1__U5Imm1_2__U5Imm1_3__U5Imm1_4
  { CVT_95_addRegGPRCOperands, 1, CVT_Tied, 0, CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegGPRC1_1__Tie0__RegGPRC1_2__U5Imm1_3__U5Imm1_4__U5Imm1_5
  { CVT_95_addRegGPRCOperands, 2, CVT_Tied, 0, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_95_addImmOperands, 6, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3__U5Imm1_4
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4__U5Imm1_5
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_95_addImmOperands, 6, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_95_addImmOperands, 5, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3__U5Imm1_4__U5Imm1_5
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_95_addImmOperands, 5, CVT_95_addImmOperands, 6, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__imm_0
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_imm_0, 0, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__imm_0
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_imm_0, 0, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__imm_0
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addImmOperands, 3, CVT_imm_0, 0, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__imm_0
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addImmOperands, 4, CVT_imm_0, 0, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2__imm_0__imm_31
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_imm_0, 0, CVT_imm_31, 0, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3__imm_0__imm_31
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_imm_0, 0, CVT_imm_31, 0, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__imm_0__imm_31
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 3, CVT_imm_0, 0, CVT_imm_31, 0, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__imm_0__imm_31
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_95_addImmOperands, 4, CVT_imm_0, 0, CVT_imm_31, 0, CVT_Done },
  // Convert__Imm1_0
  { CVT_95_addImmOperands, 1, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegGPRCOperands, 4, CVT_Done },
  // Convert__imm_0__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_imm_0, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__imm_0__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_imm_0, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegG8RC1_1__RegGxRCNoR01_2__RegGxRC1_3
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_95_addRegGxRCOperands, 4, CVT_Done },
  // Convert__imm_0__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2
  { CVT_imm_0, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__imm_0__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_imm_0, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__imm_0__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_imm_0, 0, CVT_95_addRegF8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__imm_0__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_imm_0, 0, CVT_95_addRegF8RCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__imm_0__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2
  { CVT_imm_0, 0, CVT_95_addRegF4RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_Done },
  // Convert__imm_0__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2
  { CVT_imm_0, 0, CVT_95_addRegF4RCOperands, 1, CVT_95_addRegGxRCNoR0Operands, 2, CVT_95_addRegGxRCOperands, 3, CVT_Done },
  // Convert__RegGPRC1_1__RegGxRCNoR01_2__RegGxRC1_3
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGxRCNoR0Operands, 3, CVT_95_addRegGxRCOperands, 4, CVT_Done },
  // Convert__RegG8RC1_0__RegG8RC1_2__RegG8RC1_1
  { CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 3, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__RegG8RC1_1__RegG8RC1_3__RegG8RC1_2
  { CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 4, CVT_95_addRegG8RCOperands, 3, CVT_Done },
  // Convert__U5Imm1_0__RegG8RC1_1__RegG8RC1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addRegG8RCOperands, 3, CVT_Done },
  // Convert__imm_4__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_4, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_4__RegG8RC1_0__S16Imm1_1
  { CVT_imm_4, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_12__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_12, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_12__RegG8RC1_0__S16Imm1_1
  { CVT_imm_12, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_8__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_8, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_8__RegG8RC1_0__S16Imm1_1
  { CVT_imm_8, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__U5Imm1_0__RegG8RC1_1__S16Imm1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__imm_20__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_20, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_20__RegG8RC1_0__S16Imm1_1
  { CVT_imm_20, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_5__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_5, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_5__RegG8RC1_0__S16Imm1_1
  { CVT_imm_5, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_1__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_1, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_1__RegG8RC1_0__S16Imm1_1
  { CVT_imm_1, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_6__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_6, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_6__RegG8RC1_0__S16Imm1_1
  { CVT_imm_6, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_2__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_2, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_2__RegG8RC1_0__S16Imm1_1
  { CVT_imm_2, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_16__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_16, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_16__RegG8RC1_0__S16Imm1_1
  { CVT_imm_16, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_24__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_24, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_24__RegG8RC1_0__S16Imm1_1
  { CVT_imm_24, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_31__RegG8RC1_0__RegG8RC1_1
  { CVT_imm_31, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addRegG8RCOperands, 2, CVT_Done },
  // Convert__imm_31__RegG8RC1_0__S16Imm1_1
  { CVT_imm_31, 0, CVT_95_addRegG8RCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__regR0__RegGPRC1_0
  { CVT_regR0, 0, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_1__RegGPRC1_0
  { CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 1, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__Imm1_2
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addImmOperands, 3, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__imm_0
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_imm_0, 0, CVT_Done },
  // Convert__RegGPRC1_0__RegGPRC1_1__imm_1
  { CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_imm_1, 0, CVT_Done },
  // Convert__U5Imm1_0__RegGPRC1_1__RegGPRC1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addRegGPRCOperands, 3, CVT_Done },
  // Convert__imm_4__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_4, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_4__RegGPRC1_0__S16Imm1_1
  { CVT_imm_4, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_12__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_12, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_12__RegGPRC1_0__S16Imm1_1
  { CVT_imm_12, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_8__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_8, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_8__RegGPRC1_0__S16Imm1_1
  { CVT_imm_8, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__U5Imm1_0__RegGPRC1_1__S16Imm1_2
  { CVT_95_addImmOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_95_addS16ImmOperands, 3, CVT_Done },
  // Convert__imm_20__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_20, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_20__RegGPRC1_0__S16Imm1_1
  { CVT_imm_20, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_5__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_5, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_5__RegGPRC1_0__S16Imm1_1
  { CVT_imm_5, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_1__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_1, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_1__RegGPRC1_0__S16Imm1_1
  { CVT_imm_1, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_6__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_6, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_6__RegGPRC1_0__S16Imm1_1
  { CVT_imm_6, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_2__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_2, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_2__RegGPRC1_0__S16Imm1_1
  { CVT_imm_2, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_16__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_16, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_16__RegGPRC1_0__S16Imm1_1
  { CVT_imm_16, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_24__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_24, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_24__RegGPRC1_0__S16Imm1_1
  { CVT_imm_24, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__imm_31__RegGPRC1_0__RegGPRC1_1
  { CVT_imm_31, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addRegGPRCOperands, 2, CVT_Done },
  // Convert__imm_31__RegGPRC1_0__S16Imm1_1
  { CVT_imm_31, 0, CVT_95_addRegGPRCOperands, 1, CVT_95_addS16ImmOperands, 2, CVT_Done },
  // Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addRegVRRCOperands, 2, CVT_95_addRegVRRCOperands, 3, CVT_Done },
  // Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addImmOperands, 3, CVT_95_addRegVRRCOperands, 2, CVT_Done },
  // Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3
  { CVT_95_addRegVRRCOperands, 2, CVT_95_addRegVRRCOperands, 3, CVT_95_addRegVRRCOperands, 4, CVT_Done },
  // Convert__RegVRRC1_0__RegVRRC1_1
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addRegVRRCOperands, 2, CVT_Done },
  // Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addRegVRRCOperands, 2, CVT_95_addRegVRRCOperands, 3, CVT_95_addRegVRRCOperands, 4, CVT_Done },
  // Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__U5Imm1_3
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addRegVRRCOperands, 2, CVT_95_addRegVRRCOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegVRRC1_0__S5Imm1_1
  { CVT_95_addRegVRRCOperands, 1, CVT_95_addImmOperands, 2, CVT_Done },
  // Convert__regR0__regR0__imm_0
  { CVT_regR0, 0, CVT_regR0, 0, CVT_imm_0, 0, CVT_Done },
  // Convert__RegVSFRC1_0__RegVSFRC1_1
  { CVT_95_addRegVSFRCOperands, 1, CVT_95_addRegVSFRCOperands, 2, CVT_Done },
  // Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2
  { CVT_95_addRegVSFRCOperands, 1, CVT_95_addRegVSFRCOperands, 2, CVT_95_addRegVSFRCOperands, 3, CVT_Done },
  // Convert__RegCRRC1_0__RegVSFRC1_1__RegVSFRC1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegVSFRCOperands, 2, CVT_95_addRegVSFRCOperands, 3, CVT_Done },
  // Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2
  { CVT_95_addRegVSFRCOperands, 1, CVT_Tied, 0, CVT_95_addRegVSFRCOperands, 2, CVT_95_addRegVSFRCOperands, 3, CVT_Done },
  // Convert__RegCRRC1_0__RegVSFRC1_1
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegVSFRCOperands, 2, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_Done },
  // Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3
  { CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_95_addRegVSRCOperands, 4, CVT_Done },
  // Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2
  { CVT_95_addRegVSRCOperands, 1, CVT_Tied, 0, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 2, CVT_Done },
  // Convert__RegCRRC1_0__RegVSRC1_1__RegVSRC1_2
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_Done },
  // Convert__RegCRRC1_0__RegVSRC1_1
  { CVT_95_addRegCRRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__imm_0
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_imm_0, 0, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__imm_3
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_imm_3, 0, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__U2Imm1_3
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_95_addImmOperands, 4, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 3, CVT_95_addRegVSRCOperands, 4, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_0
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 2, CVT_imm_0, 0, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_3
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 2, CVT_imm_3, 0, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__U2Imm1_2
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addImmOperands, 3, CVT_Done },
  // Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_2
  { CVT_95_addRegVSRCOperands, 1, CVT_95_addRegVSRCOperands, 2, CVT_95_addRegVSRCOperands, 2, CVT_imm_2, 0, CVT_Done },
};

void PPCAsmParser::
convertToMCInst(unsigned Kind, MCInst &Inst, unsigned Opcode,
                const OperandVector &Operands) {
  assert(Kind < CVT_NUM_SIGNATURES && "Invalid signature!");
  const uint8_t *Converter = ConversionTable[Kind];
  Inst.setOpcode(Opcode);
  for (const uint8_t *p = Converter; *p; p+= 2) {
    switch (*p) {
    default: llvm_unreachable("invalid conversion entry!");
    case CVT_Reg:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegOperands(Inst, 1);
      break;
    case CVT_Tied:
      Inst.addOperand(Inst.getOperand(*(p + 1)));
      break;
    case CVT_95_addRegG8RCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegG8RCOperands(Inst, 1);
      break;
    case CVT_95_addTLSRegOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addTLSRegOperands(Inst, 1);
      break;
    case CVT_95_addRegGPRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegGPRCOperands(Inst, 1);
      break;
    case CVT_95_addRegGPRCNoR0Operands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegGPRCNoR0Operands(Inst, 1);
      break;
    case CVT_95_addS16ImmOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addS16ImmOperands(Inst, 1);
      break;
    case CVT_95_addU16ImmOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addU16ImmOperands(Inst, 1);
      break;
    case CVT_95_addBranchTargetOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addBranchTargetOperands(Inst, 1);
      break;
    case CVT_95_addImmOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addImmOperands(Inst, 1);
      break;
    case CVT_95_addRegCRBITRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegCRBITRCOperands(Inst, 1);
      break;
    case CVT_imm_0:
      Inst.addOperand(MCOperand::CreateImm(0));
      break;
    case CVT_imm_8:
      Inst.addOperand(MCOperand::CreateImm(8));
      break;
    case CVT_imm_2:
      Inst.addOperand(MCOperand::CreateImm(2));
      break;
    case CVT_imm_10:
      Inst.addOperand(MCOperand::CreateImm(10));
      break;
    case CVT_imm_76:
      Inst.addOperand(MCOperand::CreateImm(76));
      break;
    case CVT_regCR0:
      Inst.addOperand(MCOperand::CreateReg(PPC::CR0));
      break;
    case CVT_95_addRegCRRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegCRRCOperands(Inst, 1);
      break;
    case CVT_imm_79:
      Inst.addOperand(MCOperand::CreateImm(79));
      break;
    case CVT_imm_78:
      Inst.addOperand(MCOperand::CreateImm(78));
      break;
    case CVT_imm_4:
      Inst.addOperand(MCOperand::CreateImm(4));
      break;
    case CVT_imm_7:
      Inst.addOperand(MCOperand::CreateImm(7));
      break;
    case CVT_imm_6:
      Inst.addOperand(MCOperand::CreateImm(6));
      break;
    case CVT_imm_44:
      Inst.addOperand(MCOperand::CreateImm(44));
      break;
    case CVT_imm_47:
      Inst.addOperand(MCOperand::CreateImm(47));
      break;
    case CVT_imm_46:
      Inst.addOperand(MCOperand::CreateImm(46));
      break;
    case CVT_imm_36:
      Inst.addOperand(MCOperand::CreateImm(36));
      break;
    case CVT_imm_39:
      Inst.addOperand(MCOperand::CreateImm(39));
      break;
    case CVT_imm_38:
      Inst.addOperand(MCOperand::CreateImm(38));
      break;
    case CVT_imm_12:
      Inst.addOperand(MCOperand::CreateImm(12));
      break;
    case CVT_imm_15:
      Inst.addOperand(MCOperand::CreateImm(15));
      break;
    case CVT_imm_14:
      Inst.addOperand(MCOperand::CreateImm(14));
      break;
    case CVT_imm_68:
      Inst.addOperand(MCOperand::CreateImm(68));
      break;
    case CVT_imm_71:
      Inst.addOperand(MCOperand::CreateImm(71));
      break;
    case CVT_imm_70:
      Inst.addOperand(MCOperand::CreateImm(70));
      break;
    case CVT_imm_100:
      Inst.addOperand(MCOperand::CreateImm(100));
      break;
    case CVT_imm_103:
      Inst.addOperand(MCOperand::CreateImm(103));
      break;
    case CVT_imm_102:
      Inst.addOperand(MCOperand::CreateImm(102));
      break;
    case CVT_imm_108:
      Inst.addOperand(MCOperand::CreateImm(108));
      break;
    case CVT_imm_111:
      Inst.addOperand(MCOperand::CreateImm(111));
      break;
    case CVT_imm_110:
      Inst.addOperand(MCOperand::CreateImm(110));
      break;
    case CVT_imm_31:
      Inst.addOperand(MCOperand::CreateImm(31));
      break;
    case CVT_95_addRegGxRCNoR0Operands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegGxRCNoR0Operands(Inst, 1);
      break;
    case CVT_95_addRegGxRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegGxRCOperands(Inst, 1);
      break;
    case CVT_regR0:
      Inst.addOperand(MCOperand::CreateReg(PPC::R0));
      break;
    case CVT_95_addRegF4RCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegF4RCOperands(Inst, 1);
      break;
    case CVT_95_addRegF8RCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegF8RCOperands(Inst, 1);
      break;
    case CVT_95_addRegVRRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegVRRCOperands(Inst, 1);
      break;
    case CVT_imm_1:
      Inst.addOperand(MCOperand::CreateImm(1));
      break;
    case CVT_95_addRegVSFRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegVSFRCOperands(Inst, 1);
      break;
    case CVT_95_addRegVSRCOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addRegVSRCOperands(Inst, 1);
      break;
    case CVT_imm_29:
      Inst.addOperand(MCOperand::CreateImm(29));
      break;
    case CVT_imm_280:
      Inst.addOperand(MCOperand::CreateImm(280));
      break;
    case CVT_imm_128:
      Inst.addOperand(MCOperand::CreateImm(128));
      break;
    case CVT_imm_129:
      Inst.addOperand(MCOperand::CreateImm(129));
      break;
    case CVT_imm_130:
      Inst.addOperand(MCOperand::CreateImm(130));
      break;
    case CVT_imm_131:
      Inst.addOperand(MCOperand::CreateImm(131));
      break;
    case CVT_imm_132:
      Inst.addOperand(MCOperand::CreateImm(132));
      break;
    case CVT_imm_133:
      Inst.addOperand(MCOperand::CreateImm(133));
      break;
    case CVT_imm_134:
      Inst.addOperand(MCOperand::CreateImm(134));
      break;
    case CVT_imm_135:
      Inst.addOperand(MCOperand::CreateImm(135));
      break;
    case CVT_imm_28:
      Inst.addOperand(MCOperand::CreateImm(28));
      break;
    case CVT_imm_19:
      Inst.addOperand(MCOperand::CreateImm(19));
      break;
    case CVT_imm_537:
      Inst.addOperand(MCOperand::CreateImm(537));
      break;
    case CVT_imm_539:
      Inst.addOperand(MCOperand::CreateImm(539));
      break;
    case CVT_imm_541:
      Inst.addOperand(MCOperand::CreateImm(541));
      break;
    case CVT_imm_543:
      Inst.addOperand(MCOperand::CreateImm(543));
      break;
    case CVT_imm_536:
      Inst.addOperand(MCOperand::CreateImm(536));
      break;
    case CVT_imm_538:
      Inst.addOperand(MCOperand::CreateImm(538));
      break;
    case CVT_imm_540:
      Inst.addOperand(MCOperand::CreateImm(540));
      break;
    case CVT_imm_542:
      Inst.addOperand(MCOperand::CreateImm(542));
      break;
    case CVT_imm_1018:
      Inst.addOperand(MCOperand::CreateImm(1018));
      break;
    case CVT_imm_981:
      Inst.addOperand(MCOperand::CreateImm(981));
      break;
    case CVT_imm_22:
      Inst.addOperand(MCOperand::CreateImm(22));
      break;
    case CVT_imm_17:
      Inst.addOperand(MCOperand::CreateImm(17));
      break;
    case CVT_imm_18:
      Inst.addOperand(MCOperand::CreateImm(18));
      break;
    case CVT_imm_980:
      Inst.addOperand(MCOperand::CreateImm(980));
      break;
    case CVT_imm_529:
      Inst.addOperand(MCOperand::CreateImm(529));
      break;
    case CVT_imm_531:
      Inst.addOperand(MCOperand::CreateImm(531));
      break;
    case CVT_imm_533:
      Inst.addOperand(MCOperand::CreateImm(533));
      break;
    case CVT_imm_535:
      Inst.addOperand(MCOperand::CreateImm(535));
      break;
    case CVT_imm_528:
      Inst.addOperand(MCOperand::CreateImm(528));
      break;
    case CVT_imm_530:
      Inst.addOperand(MCOperand::CreateImm(530));
      break;
    case CVT_imm_532:
      Inst.addOperand(MCOperand::CreateImm(532));
      break;
    case CVT_imm_534:
      Inst.addOperand(MCOperand::CreateImm(534));
      break;
    case CVT_imm_1019:
      Inst.addOperand(MCOperand::CreateImm(1019));
      break;
    case CVT_95_addCRBitMaskOperands:
      static_cast<PPCOperand&>(*Operands[*(p + 1)]).addCRBitMaskOperands(Inst, 1);
      break;
    case CVT_imm_48:
      Inst.addOperand(MCOperand::CreateImm(48));
      break;
    case CVT_imm_287:
      Inst.addOperand(MCOperand::CreateImm(287));
      break;
    case CVT_imm_5:
      Inst.addOperand(MCOperand::CreateImm(5));
      break;
    case CVT_imm_25:
      Inst.addOperand(MCOperand::CreateImm(25));
      break;
    case CVT_imm_512:
      Inst.addOperand(MCOperand::CreateImm(512));
      break;
    case CVT_imm_272:
      Inst.addOperand(MCOperand::CreateImm(272));
      break;
    case CVT_imm_273:
      Inst.addOperand(MCOperand::CreateImm(273));
      break;
    case CVT_imm_274:
      Inst.addOperand(MCOperand::CreateImm(274));
      break;
    case CVT_imm_275:
      Inst.addOperand(MCOperand::CreateImm(275));
      break;
    case CVT_imm_260:
      Inst.addOperand(MCOperand::CreateImm(260));
      break;
    case CVT_imm_261:
      Inst.addOperand(MCOperand::CreateImm(261));
      break;
    case CVT_imm_262:
      Inst.addOperand(MCOperand::CreateImm(262));
      break;
    case CVT_imm_263:
      Inst.addOperand(MCOperand::CreateImm(263));
      break;
    case CVT_imm_26:
      Inst.addOperand(MCOperand::CreateImm(26));
      break;
    case CVT_imm_27:
      Inst.addOperand(MCOperand::CreateImm(27));
      break;
    case CVT_imm_990:
      Inst.addOperand(MCOperand::CreateImm(990));
      break;
    case CVT_imm_991:
      Inst.addOperand(MCOperand::CreateImm(991));
      break;
    case CVT_imm_268:
      Inst.addOperand(MCOperand::CreateImm(268));
      break;
    case CVT_imm_988:
      Inst.addOperand(MCOperand::CreateImm(988));
      break;
    case CVT_imm_989:
      Inst.addOperand(MCOperand::CreateImm(989));
      break;
    case CVT_imm_269:
      Inst.addOperand(MCOperand::CreateImm(269));
      break;
    case CVT_imm_986:
      Inst.addOperand(MCOperand::CreateImm(986));
      break;
    case CVT_imm_255:
      Inst.addOperand(MCOperand::CreateImm(255));
      break;
    case CVT_imm_284:
      Inst.addOperand(MCOperand::CreateImm(284));
      break;
    case CVT_imm_285:
      Inst.addOperand(MCOperand::CreateImm(285));
      break;
    case CVT_imm_20:
      Inst.addOperand(MCOperand::CreateImm(20));
      break;
    case CVT_imm_16:
      Inst.addOperand(MCOperand::CreateImm(16));
      break;
    case CVT_imm_24:
      Inst.addOperand(MCOperand::CreateImm(24));
      break;
    case CVT_imm_3:
      Inst.addOperand(MCOperand::CreateImm(3));
      break;
    }
  }
}

void PPCAsmParser::
convertToMapAndConstraints(unsigned Kind,
                           const OperandVector &Operands) {
  assert(Kind < CVT_NUM_SIGNATURES && "Invalid signature!");
  unsigned NumMCOperands = 0;
  const uint8_t *Converter = ConversionTable[Kind];
  for (const uint8_t *p = Converter; *p; p+= 2) {
    switch (*p) {
    default: llvm_unreachable("invalid conversion entry!");
    case CVT_Reg:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("r");
      ++NumMCOperands;
      break;
    case CVT_Tied:
      ++NumMCOperands;
      break;
    case CVT_95_addRegG8RCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addTLSRegOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegGPRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegGPRCNoR0Operands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addS16ImmOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addU16ImmOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addBranchTargetOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addImmOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegCRBITRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_imm_0:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_8:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_2:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_10:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_76:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_regCR0:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      ++NumMCOperands;
      break;
    case CVT_95_addRegCRRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_imm_79:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_78:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_4:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_7:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_6:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_44:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_47:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_46:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_36:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_39:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_38:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_12:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_15:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_14:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_68:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_71:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_70:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_100:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_103:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_102:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_108:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_111:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_110:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_31:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_95_addRegGxRCNoR0Operands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegGxRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_regR0:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      ++NumMCOperands;
      break;
    case CVT_95_addRegF4RCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegF8RCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegVRRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_imm_1:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_95_addRegVSFRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_95_addRegVSRCOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_imm_29:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_280:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_128:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_129:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_130:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_131:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_132:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_133:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_134:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_135:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_28:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_19:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_537:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_539:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_541:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_543:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_536:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_538:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_540:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_542:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_1018:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_981:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_22:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_17:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_18:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_980:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_529:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_531:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_533:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_535:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_528:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_530:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_532:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_534:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_1019:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_95_addCRBitMaskOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_imm_48:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_287:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_5:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_25:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_512:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_272:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_273:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_274:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_275:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_260:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_261:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_262:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_263:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_26:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_27:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_990:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_991:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_268:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_988:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_989:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_269:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_986:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_255:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_284:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_285:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_20:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_16:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_24:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    case CVT_imm_3:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("");
      ++NumMCOperands;
      break;
    }
  }
}

namespace {

/// MatchClassKind - The kinds of classes which participate in
/// instruction matching.
enum MatchClassKind {
  InvalidMatchClass = 0,
  MCK__DOT_, // '.'
  MCK_0, // '0'
  MCK_1, // '1'
  MCK_2, // '2'
  MCK_3, // '3'
  MCK_4, // '4'
  MCK_5, // '5'
  MCK_6, // '6'
  MCK_7, // '7'
  MCK_Reg2, // derived register class
  MCK_GPRC, // register class 'GPRC'
  MCK_GPRC_NOR0, // register class 'GPRC_NOR0'
  MCK_Reg5, // derived register class
  MCK_G8RC, // register class 'G8RC'
  MCK_G8RC_NOX0, // register class 'G8RC_NOX0'
  MCK_F4RC, // register class 'F4RC,F8RC'
  MCK_VFRC, // register class 'VFRC'
  MCK_VSFRC, // register class 'VSFRC'
  MCK_VRRC, // register class 'VRRC'
  MCK_VSLRC, // register class 'VSLRC'
  MCK_VSHRC, // register class 'VSHRC'
  MCK_VSRC, // register class 'VSRC'
  MCK_CRBITRC, // register class 'CRBITRC'
  MCK_CRRC, // register class 'CRRC'
  MCK_CTRRC, // register class 'CTRRC'
  MCK_CTRRC8, // register class 'CTRRC8'
  MCK_VRSAVERC, // register class 'VRSAVERC'
  MCK_CARRYRC, // register class 'CARRYRC'
  MCK_Imm, // user defined class 'ImmAsmOperand'
  MCK_CRBitMask, // user defined class 'PPCCRBitMaskOperand'
  MCK_CondBr, // user defined class 'PPCCondBrAsmOperand'
  MCK_DirectBr, // user defined class 'PPCDirectBrAsmOperand'
  MCK_DispRI, // user defined class 'PPCDispRIOperand'
  MCK_DispRIX, // user defined class 'PPCDispRIXOperand'
  MCK_DispSPE2, // user defined class 'PPCDispSPE2Operand'
  MCK_DispSPE4, // user defined class 'PPCDispSPE4Operand'
  MCK_DispSPE8, // user defined class 'PPCDispSPE8Operand'
  MCK_RegCRBITRC, // user defined class 'PPCRegCRBITRCAsmOperand'
  MCK_RegCRRC, // user defined class 'PPCRegCRRCAsmOperand'
  MCK_RegF4RC, // user defined class 'PPCRegF4RCAsmOperand'
  MCK_RegF8RC, // user defined class 'PPCRegF8RCAsmOperand'
  MCK_RegG8RC, // user defined class 'PPCRegG8RCAsmOperand'
  MCK_RegG8RCNoX0, // user defined class 'PPCRegG8RCNoX0AsmOperand'
  MCK_RegGPRC, // user defined class 'PPCRegGPRCAsmOperand'
  MCK_RegGPRCNoR0, // user defined class 'PPCRegGPRCNoR0AsmOperand'
  MCK_RegGxRCNoR0, // user defined class 'PPCRegGxRCNoR0Operand'
  MCK_RegGxRC, // user defined class 'PPCRegGxRCOperand'
  MCK_RegVRRC, // user defined class 'PPCRegVRRCAsmOperand'
  MCK_RegVSFRC, // user defined class 'PPCRegVSFRCAsmOperand'
  MCK_RegVSRC, // user defined class 'PPCRegVSRCAsmOperand'
  MCK_S16Imm, // user defined class 'PPCS16ImmAsmOperand'
  MCK_S17Imm, // user defined class 'PPCS17ImmAsmOperand'
  MCK_S5Imm, // user defined class 'PPCS5ImmAsmOperand'
  MCK_TLSReg, // user defined class 'PPCTLSRegOperand'
  MCK_U16Imm, // user defined class 'PPCU16ImmAsmOperand'
  MCK_U2Imm, // user defined class 'PPCU2ImmAsmOperand'
  MCK_U4Imm, // user defined class 'PPCU4ImmAsmOperand'
  MCK_U5Imm, // user defined class 'PPCU5ImmAsmOperand'
  MCK_U6Imm, // user defined class 'PPCU6ImmAsmOperand'
  NumMatchClassKinds
};

}

static MatchClassKind matchTokenString(StringRef Name) {
  switch (Name.size()) {
  default: break;
  case 1:	 // 9 strings to match.
    switch (Name[0]) {
    default: break;
    case '.':	 // 1 string to match.
      return MCK__DOT_;	 // "."
    case '0':	 // 1 string to match.
      return MCK_0;	 // "0"
    case '1':	 // 1 string to match.
      return MCK_1;	 // "1"
    case '2':	 // 1 string to match.
      return MCK_2;	 // "2"
    case '3':	 // 1 string to match.
      return MCK_3;	 // "3"
    case '4':	 // 1 string to match.
      return MCK_4;	 // "4"
    case '5':	 // 1 string to match.
      return MCK_5;	 // "5"
    case '6':	 // 1 string to match.
      return MCK_6;	 // "6"
    case '7':	 // 1 string to match.
      return MCK_7;	 // "7"
    }
    break;
  }
  return InvalidMatchClass;
}

/// isSubclass - Compute whether \p A is a subclass of \p B.
static bool isSubclass(MatchClassKind A, MatchClassKind B) {
  if (A == B)
    return true;

  switch (A) {
  default:
    return false;

  case MCK_Reg2:
    switch (B) {
    default: return false;
    case MCK_GPRC: return true;
    case MCK_GPRC_NOR0: return true;
    }

  case MCK_Reg5:
    switch (B) {
    default: return false;
    case MCK_G8RC: return true;
    case MCK_G8RC_NOX0: return true;
    }

  case MCK_F4RC:
    return B == MCK_VSFRC;

  case MCK_VFRC:
    return B == MCK_VSFRC;

  case MCK_VSLRC:
    return B == MCK_VSRC;

  case MCK_VSHRC:
    return B == MCK_VSRC;
  }
}

static unsigned validateOperandClass(MCParsedAsmOperand &GOp, MatchClassKind Kind) {
  PPCOperand &Operand = (PPCOperand&)GOp;
  if (Kind == InvalidMatchClass)
    return MCTargetAsmParser::Match_InvalidOperand;

  if (Operand.isToken())
    return isSubclass(matchTokenString(Operand.getToken()), Kind) ?
             MCTargetAsmParser::Match_Success :
             MCTargetAsmParser::Match_InvalidOperand;

  // 'Imm' class
  if (Kind == MCK_Imm) {
    if (Operand.isImm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'CRBitMask' class
  if (Kind == MCK_CRBitMask) {
    if (Operand.isCRBitMask())
      return MCTargetAsmParser::Match_Success;
  }

  // 'CondBr' class
  if (Kind == MCK_CondBr) {
    if (Operand.isCondBr())
      return MCTargetAsmParser::Match_Success;
  }

  // 'DirectBr' class
  if (Kind == MCK_DirectBr) {
    if (Operand.isDirectBr())
      return MCTargetAsmParser::Match_Success;
  }

  // 'DispRI' class
  if (Kind == MCK_DispRI) {
    if (Operand.isS16Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'DispRIX' class
  if (Kind == MCK_DispRIX) {
    if (Operand.isS16ImmX4())
      return MCTargetAsmParser::Match_Success;
  }

  // 'DispSPE2' class
  if (Kind == MCK_DispSPE2) {
    if (Operand.isU6ImmX2())
      return MCTargetAsmParser::Match_Success;
  }

  // 'DispSPE4' class
  if (Kind == MCK_DispSPE4) {
    if (Operand.isU7ImmX4())
      return MCTargetAsmParser::Match_Success;
  }

  // 'DispSPE8' class
  if (Kind == MCK_DispSPE8) {
    if (Operand.isU8ImmX8())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegCRBITRC' class
  if (Kind == MCK_RegCRBITRC) {
    if (Operand.isCRBitNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegCRRC' class
  if (Kind == MCK_RegCRRC) {
    if (Operand.isCCRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegF4RC' class
  if (Kind == MCK_RegF4RC) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegF8RC' class
  if (Kind == MCK_RegF8RC) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegG8RC' class
  if (Kind == MCK_RegG8RC) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegG8RCNoX0' class
  if (Kind == MCK_RegG8RCNoX0) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegGPRC' class
  if (Kind == MCK_RegGPRC) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegGPRCNoR0' class
  if (Kind == MCK_RegGPRCNoR0) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegGxRCNoR0' class
  if (Kind == MCK_RegGxRCNoR0) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegGxRC' class
  if (Kind == MCK_RegGxRC) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegVRRC' class
  if (Kind == MCK_RegVRRC) {
    if (Operand.isRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegVSFRC' class
  if (Kind == MCK_RegVSFRC) {
    if (Operand.isVSRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'RegVSRC' class
  if (Kind == MCK_RegVSRC) {
    if (Operand.isVSRegNumber())
      return MCTargetAsmParser::Match_Success;
  }

  // 'S16Imm' class
  if (Kind == MCK_S16Imm) {
    if (Operand.isS16Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'S17Imm' class
  if (Kind == MCK_S17Imm) {
    if (Operand.isS17Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'S5Imm' class
  if (Kind == MCK_S5Imm) {
    if (Operand.isS5Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'TLSReg' class
  if (Kind == MCK_TLSReg) {
    if (Operand.isTLSReg())
      return MCTargetAsmParser::Match_Success;
  }

  // 'U16Imm' class
  if (Kind == MCK_U16Imm) {
    if (Operand.isU16Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'U2Imm' class
  if (Kind == MCK_U2Imm) {
    if (Operand.isU2Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'U4Imm' class
  if (Kind == MCK_U4Imm) {
    if (Operand.isU4Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'U5Imm' class
  if (Kind == MCK_U5Imm) {
    if (Operand.isU5Imm())
      return MCTargetAsmParser::Match_Success;
  }

  // 'U6Imm' class
  if (Kind == MCK_U6Imm) {
    if (Operand.isU6Imm())
      return MCTargetAsmParser::Match_Success;
  }

  if (Operand.isReg()) {
    MatchClassKind OpKind;
    switch (Operand.getReg()) {
    default: OpKind = InvalidMatchClass; break;
    case PPC::R0: OpKind = MCK_GPRC; break;
    case PPC::R1: OpKind = MCK_Reg2; break;
    case PPC::R2: OpKind = MCK_Reg2; break;
    case PPC::R3: OpKind = MCK_Reg2; break;
    case PPC::R4: OpKind = MCK_Reg2; break;
    case PPC::R5: OpKind = MCK_Reg2; break;
    case PPC::R6: OpKind = MCK_Reg2; break;
    case PPC::R7: OpKind = MCK_Reg2; break;
    case PPC::R8: OpKind = MCK_Reg2; break;
    case PPC::R9: OpKind = MCK_Reg2; break;
    case PPC::R10: OpKind = MCK_Reg2; break;
    case PPC::R11: OpKind = MCK_Reg2; break;
    case PPC::R12: OpKind = MCK_Reg2; break;
    case PPC::R13: OpKind = MCK_Reg2; break;
    case PPC::R14: OpKind = MCK_Reg2; break;
    case PPC::R15: OpKind = MCK_Reg2; break;
    case PPC::R16: OpKind = MCK_Reg2; break;
    case PPC::R17: OpKind = MCK_Reg2; break;
    case PPC::R18: OpKind = MCK_Reg2; break;
    case PPC::R19: OpKind = MCK_Reg2; break;
    case PPC::R20: OpKind = MCK_Reg2; break;
    case PPC::R21: OpKind = MCK_Reg2; break;
    case PPC::R22: OpKind = MCK_Reg2; break;
    case PPC::R23: OpKind = MCK_Reg2; break;
    case PPC::R24: OpKind = MCK_Reg2; break;
    case PPC::R25: OpKind = MCK_Reg2; break;
    case PPC::R26: OpKind = MCK_Reg2; break;
    case PPC::R27: OpKind = MCK_Reg2; break;
    case PPC::R28: OpKind = MCK_Reg2; break;
    case PPC::R29: OpKind = MCK_Reg2; break;
    case PPC::R30: OpKind = MCK_Reg2; break;
    case PPC::R31: OpKind = MCK_Reg2; break;
    case PPC::X0: OpKind = MCK_G8RC; break;
    case PPC::X1: OpKind = MCK_Reg5; break;
    case PPC::X2: OpKind = MCK_Reg5; break;
    case PPC::X3: OpKind = MCK_Reg5; break;
    case PPC::X4: OpKind = MCK_Reg5; break;
    case PPC::X5: OpKind = MCK_Reg5; break;
    case PPC::X6: OpKind = MCK_Reg5; break;
    case PPC::X7: OpKind = MCK_Reg5; break;
    case PPC::X8: OpKind = MCK_Reg5; break;
    case PPC::X9: OpKind = MCK_Reg5; break;
    case PPC::X10: OpKind = MCK_Reg5; break;
    case PPC::X11: OpKind = MCK_Reg5; break;
    case PPC::X12: OpKind = MCK_Reg5; break;
    case PPC::X13: OpKind = MCK_Reg5; break;
    case PPC::X14: OpKind = MCK_Reg5; break;
    case PPC::X15: OpKind = MCK_Reg5; break;
    case PPC::X16: OpKind = MCK_Reg5; break;
    case PPC::X17: OpKind = MCK_Reg5; break;
    case PPC::X18: OpKind = MCK_Reg5; break;
    case PPC::X19: OpKind = MCK_Reg5; break;
    case PPC::X20: OpKind = MCK_Reg5; break;
    case PPC::X21: OpKind = MCK_Reg5; break;
    case PPC::X22: OpKind = MCK_Reg5; break;
    case PPC::X23: OpKind = MCK_Reg5; break;
    case PPC::X24: OpKind = MCK_Reg5; break;
    case PPC::X25: OpKind = MCK_Reg5; break;
    case PPC::X26: OpKind = MCK_Reg5; break;
    case PPC::X27: OpKind = MCK_Reg5; break;
    case PPC::X28: OpKind = MCK_Reg5; break;
    case PPC::X29: OpKind = MCK_Reg5; break;
    case PPC::X30: OpKind = MCK_Reg5; break;
    case PPC::X31: OpKind = MCK_Reg5; break;
    case PPC::F0: OpKind = MCK_F4RC; break;
    case PPC::F1: OpKind = MCK_F4RC; break;
    case PPC::F2: OpKind = MCK_F4RC; break;
    case PPC::F3: OpKind = MCK_F4RC; break;
    case PPC::F4: OpKind = MCK_F4RC; break;
    case PPC::F5: OpKind = MCK_F4RC; break;
    case PPC::F6: OpKind = MCK_F4RC; break;
    case PPC::F7: OpKind = MCK_F4RC; break;
    case PPC::F8: OpKind = MCK_F4RC; break;
    case PPC::F9: OpKind = MCK_F4RC; break;
    case PPC::F10: OpKind = MCK_F4RC; break;
    case PPC::F11: OpKind = MCK_F4RC; break;
    case PPC::F12: OpKind = MCK_F4RC; break;
    case PPC::F13: OpKind = MCK_F4RC; break;
    case PPC::F14: OpKind = MCK_F4RC; break;
    case PPC::F15: OpKind = MCK_F4RC; break;
    case PPC::F16: OpKind = MCK_F4RC; break;
    case PPC::F17: OpKind = MCK_F4RC; break;
    case PPC::F18: OpKind = MCK_F4RC; break;
    case PPC::F19: OpKind = MCK_F4RC; break;
    case PPC::F20: OpKind = MCK_F4RC; break;
    case PPC::F21: OpKind = MCK_F4RC; break;
    case PPC::F22: OpKind = MCK_F4RC; break;
    case PPC::F23: OpKind = MCK_F4RC; break;
    case PPC::F24: OpKind = MCK_F4RC; break;
    case PPC::F25: OpKind = MCK_F4RC; break;
    case PPC::F26: OpKind = MCK_F4RC; break;
    case PPC::F27: OpKind = MCK_F4RC; break;
    case PPC::F28: OpKind = MCK_F4RC; break;
    case PPC::F29: OpKind = MCK_F4RC; break;
    case PPC::F30: OpKind = MCK_F4RC; break;
    case PPC::F31: OpKind = MCK_F4RC; break;
    case PPC::VF0: OpKind = MCK_VFRC; break;
    case PPC::VF1: OpKind = MCK_VFRC; break;
    case PPC::VF2: OpKind = MCK_VFRC; break;
    case PPC::VF3: OpKind = MCK_VFRC; break;
    case PPC::VF4: OpKind = MCK_VFRC; break;
    case PPC::VF5: OpKind = MCK_VFRC; break;
    case PPC::VF6: OpKind = MCK_VFRC; break;
    case PPC::VF7: OpKind = MCK_VFRC; break;
    case PPC::VF8: OpKind = MCK_VFRC; break;
    case PPC::VF9: OpKind = MCK_VFRC; break;
    case PPC::VF10: OpKind = MCK_VFRC; break;
    case PPC::VF11: OpKind = MCK_VFRC; break;
    case PPC::VF12: OpKind = MCK_VFRC; break;
    case PPC::VF13: OpKind = MCK_VFRC; break;
    case PPC::VF14: OpKind = MCK_VFRC; break;
    case PPC::VF15: OpKind = MCK_VFRC; break;
    case PPC::VF16: OpKind = MCK_VFRC; break;
    case PPC::VF17: OpKind = MCK_VFRC; break;
    case PPC::VF18: OpKind = MCK_VFRC; break;
    case PPC::VF19: OpKind = MCK_VFRC; break;
    case PPC::VF20: OpKind = MCK_VFRC; break;
    case PPC::VF21: OpKind = MCK_VFRC; break;
    case PPC::VF22: OpKind = MCK_VFRC; break;
    case PPC::VF23: OpKind = MCK_VFRC; break;
    case PPC::VF24: OpKind = MCK_VFRC; break;
    case PPC::VF25: OpKind = MCK_VFRC; break;
    case PPC::VF26: OpKind = MCK_VFRC; break;
    case PPC::VF27: OpKind = MCK_VFRC; break;
    case PPC::VF28: OpKind = MCK_VFRC; break;
    case PPC::VF29: OpKind = MCK_VFRC; break;
    case PPC::VF30: OpKind = MCK_VFRC; break;
    case PPC::VF31: OpKind = MCK_VFRC; break;
    case PPC::V0: OpKind = MCK_VRRC; break;
    case PPC::V1: OpKind = MCK_VRRC; break;
    case PPC::V2: OpKind = MCK_VRRC; break;
    case PPC::V3: OpKind = MCK_VRRC; break;
    case PPC::V4: OpKind = MCK_VRRC; break;
    case PPC::V5: OpKind = MCK_VRRC; break;
    case PPC::V6: OpKind = MCK_VRRC; break;
    case PPC::V7: OpKind = MCK_VRRC; break;
    case PPC::V8: OpKind = MCK_VRRC; break;
    case PPC::V9: OpKind = MCK_VRRC; break;
    case PPC::V10: OpKind = MCK_VRRC; break;
    case PPC::V11: OpKind = MCK_VRRC; break;
    case PPC::V12: OpKind = MCK_VRRC; break;
    case PPC::V13: OpKind = MCK_VRRC; break;
    case PPC::V14: OpKind = MCK_VRRC; break;
    case PPC::V15: OpKind = MCK_VRRC; break;
    case PPC::V16: OpKind = MCK_VRRC; break;
    case PPC::V17: OpKind = MCK_VRRC; break;
    case PPC::V18: OpKind = MCK_VRRC; break;
    case PPC::V19: OpKind = MCK_VRRC; break;
    case PPC::V20: OpKind = MCK_VRRC; break;
    case PPC::V21: OpKind = MCK_VRRC; break;
    case PPC::V22: OpKind = MCK_VRRC; break;
    case PPC::V23: OpKind = MCK_VRRC; break;
    case PPC::V24: OpKind = MCK_VRRC; break;
    case PPC::V25: OpKind = MCK_VRRC; break;
    case PPC::V26: OpKind = MCK_VRRC; break;
    case PPC::V27: OpKind = MCK_VRRC; break;
    case PPC::V28: OpKind = MCK_VRRC; break;
    case PPC::V29: OpKind = MCK_VRRC; break;
    case PPC::V30: OpKind = MCK_VRRC; break;
    case PPC::V31: OpKind = MCK_VRRC; break;
    case PPC::VSL0: OpKind = MCK_VSLRC; break;
    case PPC::VSL1: OpKind = MCK_VSLRC; break;
    case PPC::VSL2: OpKind = MCK_VSLRC; break;
    case PPC::VSL3: OpKind = MCK_VSLRC; break;
    case PPC::VSL4: OpKind = MCK_VSLRC; break;
    case PPC::VSL5: OpKind = MCK_VSLRC; break;
    case PPC::VSL6: OpKind = MCK_VSLRC; break;
    case PPC::VSL7: OpKind = MCK_VSLRC; break;
    case PPC::VSL8: OpKind = MCK_VSLRC; break;
    case PPC::VSL9: OpKind = MCK_VSLRC; break;
    case PPC::VSL10: OpKind = MCK_VSLRC; break;
    case PPC::VSL11: OpKind = MCK_VSLRC; break;
    case PPC::VSL12: OpKind = MCK_VSLRC; break;
    case PPC::VSL13: OpKind = MCK_VSLRC; break;
    case PPC::VSL14: OpKind = MCK_VSLRC; break;
    case PPC::VSL15: OpKind = MCK_VSLRC; break;
    case PPC::VSL16: OpKind = MCK_VSLRC; break;
    case PPC::VSL17: OpKind = MCK_VSLRC; break;
    case PPC::VSL18: OpKind = MCK_VSLRC; break;
    case PPC::VSL19: OpKind = MCK_VSLRC; break;
    case PPC::VSL20: OpKind = MCK_VSLRC; break;
    case PPC::VSL21: OpKind = MCK_VSLRC; break;
    case PPC::VSL22: OpKind = MCK_VSLRC; break;
    case PPC::VSL23: OpKind = MCK_VSLRC; break;
    case PPC::VSL24: OpKind = MCK_VSLRC; break;
    case PPC::VSL25: OpKind = MCK_VSLRC; break;
    case PPC::VSL26: OpKind = MCK_VSLRC; break;
    case PPC::VSL27: OpKind = MCK_VSLRC; break;
    case PPC::VSL28: OpKind = MCK_VSLRC; break;
    case PPC::VSL29: OpKind = MCK_VSLRC; break;
    case PPC::VSL30: OpKind = MCK_VSLRC; break;
    case PPC::VSL31: OpKind = MCK_VSLRC; break;
    case PPC::VSH0: OpKind = MCK_VSHRC; break;
    case PPC::VSH1: OpKind = MCK_VSHRC; break;
    case PPC::VSH2: OpKind = MCK_VSHRC; break;
    case PPC::VSH3: OpKind = MCK_VSHRC; break;
    case PPC::VSH4: OpKind = MCK_VSHRC; break;
    case PPC::VSH5: OpKind = MCK_VSHRC; break;
    case PPC::VSH6: OpKind = MCK_VSHRC; break;
    case PPC::VSH7: OpKind = MCK_VSHRC; break;
    case PPC::VSH8: OpKind = MCK_VSHRC; break;
    case PPC::VSH9: OpKind = MCK_VSHRC; break;
    case PPC::VSH10: OpKind = MCK_VSHRC; break;
    case PPC::VSH11: OpKind = MCK_VSHRC; break;
    case PPC::VSH12: OpKind = MCK_VSHRC; break;
    case PPC::VSH13: OpKind = MCK_VSHRC; break;
    case PPC::VSH14: OpKind = MCK_VSHRC; break;
    case PPC::VSH15: OpKind = MCK_VSHRC; break;
    case PPC::VSH16: OpKind = MCK_VSHRC; break;
    case PPC::VSH17: OpKind = MCK_VSHRC; break;
    case PPC::VSH18: OpKind = MCK_VSHRC; break;
    case PPC::VSH19: OpKind = MCK_VSHRC; break;
    case PPC::VSH20: OpKind = MCK_VSHRC; break;
    case PPC::VSH21: OpKind = MCK_VSHRC; break;
    case PPC::VSH22: OpKind = MCK_VSHRC; break;
    case PPC::VSH23: OpKind = MCK_VSHRC; break;
    case PPC::VSH24: OpKind = MCK_VSHRC; break;
    case PPC::VSH25: OpKind = MCK_VSHRC; break;
    case PPC::VSH26: OpKind = MCK_VSHRC; break;
    case PPC::VSH27: OpKind = MCK_VSHRC; break;
    case PPC::VSH28: OpKind = MCK_VSHRC; break;
    case PPC::VSH29: OpKind = MCK_VSHRC; break;
    case PPC::VSH30: OpKind = MCK_VSHRC; break;
    case PPC::VSH31: OpKind = MCK_VSHRC; break;
    case PPC::ZERO: OpKind = MCK_GPRC_NOR0; break;
    case PPC::ZERO8: OpKind = MCK_G8RC_NOX0; break;
    case PPC::FP: OpKind = MCK_Reg2; break;
    case PPC::FP8: OpKind = MCK_Reg5; break;
    case PPC::BP: OpKind = MCK_Reg2; break;
    case PPC::BP8: OpKind = MCK_Reg5; break;
    case PPC::CR0LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR0GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR0EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR0UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR1LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR1GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR1EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR1UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR2LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR2GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR2EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR2UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR3LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR3GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR3EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR3UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR4LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR4GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR4EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR4UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR5LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR5GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR5EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR5UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR6LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR6GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR6EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR6UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR7LT: OpKind = MCK_CRBITRC; break;
    case PPC::CR7GT: OpKind = MCK_CRBITRC; break;
    case PPC::CR7EQ: OpKind = MCK_CRBITRC; break;
    case PPC::CR7UN: OpKind = MCK_CRBITRC; break;
    case PPC::CR0: OpKind = MCK_CRRC; break;
    case PPC::CR1: OpKind = MCK_CRRC; break;
    case PPC::CR2: OpKind = MCK_CRRC; break;
    case PPC::CR3: OpKind = MCK_CRRC; break;
    case PPC::CR4: OpKind = MCK_CRRC; break;
    case PPC::CR5: OpKind = MCK_CRRC; break;
    case PPC::CR6: OpKind = MCK_CRRC; break;
    case PPC::CR7: OpKind = MCK_CRRC; break;
    case PPC::CTR: OpKind = MCK_CTRRC; break;
    case PPC::CTR8: OpKind = MCK_CTRRC8; break;
    case PPC::VRSAVE: OpKind = MCK_VRSAVERC; break;
    case PPC::CARRY: OpKind = MCK_CARRYRC; break;
    }
    return isSubclass(OpKind, Kind) ? MCTargetAsmParser::Match_Success :
                                      MCTargetAsmParser::Match_InvalidOperand;
  }

  return MCTargetAsmParser::Match_InvalidOperand;
}

uint64_t PPCAsmParser::
ComputeAvailableFeatures(uint64_t FB) const {
  uint64_t Features = 0;
  return Features;
}

static const char *const MnemonicTable =
    "\003add\004addc\004adde\004addi\005addic\005addis\005addme\005addze\003"
    "and\004andc\004andi\005andis\004attn\001b\002ba\002bc\003bca\005bcctr\006"
    "bcctrl\003bcl\004bcla\004bclr\005bclrl\004bctr\005bctrl\004bdnz\005bdnz"
    "+\005bdnz-\005bdnza\006bdnza+\006bdnza-\005bdnzf\006bdnzfa\006bdnzfl\007"
    "bdnzfla\007bdnzflr\010bdnzflrl\005bdnzl\006bdnzl+\006bdnzl-\006bdnzla\007"
    "bdnzla+\007bdnzla-\006bdnzlr\007bdnzlr+\007bdnzlr-\007bdnzlrl\010bdnzlr"
    "l+\010bdnzlrl-\005bdnzt\006bdnzta\006bdnztl\007bdnztla\007bdnztlr\010bd"
    "nztlrl\003bdz\004bdz+\004bdz-\004bdza\005bdza+\005bdza-\004bdzf\005bdzf"
    "a\005bdzfl\006bdzfla\006bdzflr\007bdzflrl\004bdzl\005bdzl+\005bdzl-\005"
    "bdzla\006bdzla+\006bdzla-\005bdzlr\006bdzlr+\006bdzlr-\006bdzlrl\007bdz"
    "lrl+\007bdzlrl-\004bdzt\005bdzta\005bdztl\006bdztla\006bdztlr\007bdztlr"
    "l\003beq\004beq+\004beq-\004beqa\005beqa+\005beqa-\006beqctr\007beqctr+"
    "\007beqctr-\007beqctrl\010beqctrl+\010beqctrl-\004beql\005beql+\005beql"
    "-\005beqla\006beqla+\006beqla-\005beqlr\006beqlr+\006beqlr-\006beqlrl\007"
    "beqlrl+\007beqlrl-\002bf\003bf+\003bf-\003bfa\004bfa+\004bfa-\005bfctr\006"
    "bfctr+\006bfctr-\006bfctrl\007bfctrl+\007bfctrl-\003bfl\004bfl+\004bfl-"
    "\004bfla\005bfla+\005bfla-\004bflr\005bflr+\005bflr-\005bflrl\006bflrl+"
    "\006bflrl-\003bge\004bge+\004bge-\004bgea\005bgea+\005bgea-\006bgectr\007"
    "bgectr+\007bgectr-\007bgectrl\010bgectrl+\010bgectrl-\004bgel\005bgel+\005"
    "bgel-\005bgela\006bgela+\006bgela-\005bgelr\006bgelr+\006bgelr-\006bgel"
    "rl\007bgelrl+\007bgelrl-\003bgt\004bgt+\004bgt-\004bgta\005bgta+\005bgt"
    "a-\006bgtctr\007bgtctr+\007bgtctr-\007bgtctrl\010bgtctrl+\010bgtctrl-\004"
    "bgtl\005bgtl+\005bgtl-\005bgtla\006bgtla+\006bgtla-\005bgtlr\006bgtlr+\006"
    "bgtlr-\006bgtlrl\007bgtlrl+\007bgtlrl-\002bl\003bla\003ble\004ble+\004b"
    "le-\004blea\005blea+\005blea-\006blectr\007blectr+\007blectr-\007blectr"
    "l\010blectrl+\010blectrl-\004blel\005blel+\005blel-\005blela\006blela+\006"
    "blela-\005blelr\006blelr+\006blelr-\006blelrl\007blelrl+\007blelrl-\003"
    "blr\004blrl\003blt\004blt+\004blt-\004blta\005blta+\005blta-\006bltctr\007"
    "bltctr+\007bltctr-\007bltctrl\010bltctrl+\010bltctrl-\004bltl\005bltl+\005"
    "bltl-\005bltla\006bltla+\006bltla-\005bltlr\006bltlr+\006bltlr-\006bltl"
    "rl\007bltlrl+\007bltlrl-\003bne\004bne+\004bne-\004bnea\005bnea+\005bne"
    "a-\006bnectr\007bnectr+\007bnectr-\007bnectrl\010bnectrl+\010bnectrl-\004"
    "bnel\005bnel+\005bnel-\005bnela\006bnela+\006bnela-\005bnelr\006bnelr+\006"
    "bnelr-\006bnelrl\007bnelrl+\007bnelrl-\003bng\004bng+\004bng-\004bnga\005"
    "bnga+\005bnga-\006bngctr\007bngctr+\007bngctr-\007bngctrl\010bngctrl+\010"
    "bngctrl-\004bngl\005bngl+\005bngl-\005bngla\006bngla+\006bngla-\005bngl"
    "r\006bnglr+\006bnglr-\006bnglrl\007bnglrl+\007bnglrl-\003bnl\004bnl+\004"
    "bnl-\004bnla\005bnla+\005bnla-\006bnlctr\007bnlctr+\007bnlctr-\007bnlct"
    "rl\010bnlctrl+\010bnlctrl-\004bnll\005bnll+\005bnll-\005bnlla\006bnlla+"
    "\006bnlla-\005bnllr\006bnllr+\006bnllr-\006bnllrl\007bnllrl+\007bnllrl-"
    "\003bns\004bns+\004bns-\004bnsa\005bnsa+\005bnsa-\006bnsctr\007bnsctr+\007"
    "bnsctr-\007bnsctrl\010bnsctrl+\010bnsctrl-\004bnsl\005bnsl+\005bnsl-\005"
    "bnsla\006bnsla+\006bnsla-\005bnslr\006bnslr+\006bnslr-\006bnslrl\007bns"
    "lrl+\007bnslrl-\003bnu\004bnu+\004bnu-\004bnua\005bnua+\005bnua-\006bnu"
    "ctr\007bnuctr+\007bnuctr-\007bnuctrl\010bnuctrl+\010bnuctrl-\004bnul\005"
    "bnul+\005bnul-\005bnula\006bnula+\006bnula-\005bnulr\006bnulr+\006bnulr"
    "-\006bnulrl\007bnulrl+\007bnulrl-\005brinc\003bso\004bso+\004bso-\004bs"
    "oa\005bsoa+\005bsoa-\006bsoctr\007bsoctr+\007bsoctr-\007bsoctrl\010bsoc"
    "trl+\010bsoctrl-\004bsol\005bsol+\005bsol-\005bsola\006bsola+\006bsola-"
    "\005bsolr\006bsolr+\006bsolr-\006bsolrl\007bsolrl+\007bsolrl-\002bt\003"
    "bt+\003bt-\003bta\004bta+\004bta-\005btctr\006btctr+\006btctr-\006btctr"
    "l\007btctrl+\007btctrl-\003btl\004btl+\004btl-\004btla\005btla+\005btla"
    "-\004btlr\005btlr+\005btlr-\005btlrl\006btlrl+\006btlrl-\003bun\004bun+"
    "\004bun-\004buna\005buna+\005buna-\006bunctr\007bunctr+\007bunctr-\007b"
    "unctrl\010bunctrl+\010bunctrl-\004bunl\005bunl+\005bunl-\005bunla\006bu"
    "nla+\006bunla-\005bunlr\006bunlr+\006bunlr-\006bunlrl\007bunlrl+\007bun"
    "lrl-\006clrldi\010clrlsldi\010clrlslwi\006clrlwi\006clrrdi\006clrrwi\003"
    "cmp\004cmpb\004cmpd\005cmpdi\004cmpi\004cmpl\005cmpld\006cmpldi\005cmpl"
    "i\005cmplw\006cmplwi\004cmpw\005cmpwi\006cntlzd\006cntlzw\005crand\006c"
    "randc\005crclr\005creqv\006crmove\006crnand\005crnor\005crnot\004cror\005"
    "crorc\005crset\005crxor\004dcba\004dcbf\004dcbi\005dcbst\004dcbt\006dcb"
    "tst\004dcbz\005dcbzl\005dccci\003dci\004divd\005divdu\004divw\005divwu\003"
    "dss\006dssall\003dst\005dstst\006dststt\004dstt\005eieio\003eqv\005evab"
    "s\007evaddiw\013evaddsmiaaw\013evaddssiaaw\013evaddumiaaw\013evaddusiaa"
    "w\006evaddw\005evand\006evandc\007evcmpeq\010evcmpgts\010evcmpgtu\010ev"
    "cmplts\010evcmpltu\010evcntlsw\010evcntlzw\007evdivws\007evdivwu\005eve"
    "qv\007evextsb\007evextsh\005evldd\006evlddx\005evldh\006evldhx\005evldw"
    "\006evldwx\013evlhhesplat\014evlhhesplatx\014evlhhossplat\015evlhhosspl"
    "atx\014evlhhousplat\015evlhhousplatx\006evlwhe\007evlwhex\007evlwhos\010"
    "evlwhosx\007evlwhou\010evlwhoux\nevlwhsplat\013evlwhsplatx\nevlwwsplat\013"
    "evlwwsplatx\tevmergehi\013evmergehilo\tevmergelo\013evmergelohi\013evmh"
    "egsmfaa\013evmhegsmfan\013evmhegsmiaa\013evmhegsmian\013evmhegumiaa\013"
    "evmhegumian\010evmhesmf\tevmhesmfa\013evmhesmfaaw\013evmhesmfanw\010evm"
    "hesmi\tevmhesmia\013evmhesmiaaw\013evmhesmianw\010evmhessf\tevmhessfa\013"
    "evmhessfaaw\013evmhessfanw\013evmhessiaaw\013evmhessianw\010evmheumi\te"
    "vmheumia\013evmheumiaaw\013evmheumianw\013evmheusiaaw\013evmheusianw\013"
    "evmhogsmfaa\013evmhogsmfan\013evmhogsmiaa\013evmhogsmian\013evmhogumiaa"
    "\013evmhogumian\010evmhosmf\tevmhosmfa\013evmhosmfaaw\013evmhosmfanw\010"
    "evmhosmi\tevmhosmia\013evmhosmiaaw\013evmhosmianw\010evmhossf\tevmhossf"
    "a\013evmhossfaaw\013evmhossfanw\013evmhossiaaw\013evmhossianw\010evmhou"
    "mi\tevmhoumia\013evmhoumiaaw\013evmhoumianw\013evmhousiaaw\013evmhousia"
    "nw\005evmra\010evmwhsmf\tevmwhsmfa\010evmwhsmi\tevmwhsmia\010evmwhssf\t"
    "evmwhssfa\010evmwhumi\tevmwhumia\013evmwlsmiaaw\013evmwlsmianw\013evmwl"
    "ssiaaw\013evmwlssianw\010evmwlumi\tevmwlumia\013evmwlumiaaw\013evmwlumi"
    "anw\013evmwlusiaaw\013evmwlusianw\007evmwsmf\010evmwsmfa\tevmwsmfaa\tev"
    "mwsmfan\007evmwsmi\010evmwsmia\tevmwsmiaa\tevmwsmian\007evmwssf\010evmw"
    "ssfa\tevmwssfaa\tevmwssfan\007evmwumi\010evmwumia\tevmwumiaa\tevmwumian"
    "\006evnand\005evneg\005evnor\004evor\005evorc\005evrlw\006evrlwi\006evr"
    "ndw\005evslw\006evslwi\tevsplatfi\010evsplati\007evsrwis\007evsrwiu\006"
    "evsrws\006evsrwu\006evstdd\007evstddx\006evstdh\007evstdhx\006evstdw\007"
    "evstdwx\007evstwhe\010evstwhex\007evstwho\010evstwhox\007evstwwe\010evs"
    "twwex\007evstwwo\010evstwwox\014evsubfsmiaaw\014evsubfssiaaw\014evsubfu"
    "miaaw\014evsubfusiaaw\007evsubfw\010evsubifw\005evxor\006extldi\006extl"
    "wi\006extrdi\006extrwi\005extsb\005extsh\005extsw\004fabs\004fadd\005fa"
    "dds\005fcfid\006fcfids\006fcfidu\007fcfidus\005fcmpu\006fcpsgn\005fctid"
    "\007fctiduz\006fctidz\005fctiw\007fctiwuz\006fctiwz\004fdiv\005fdivs\005"
    "fmadd\006fmadds\003fmr\005fmsub\006fmsubs\004fmul\005fmuls\005fnabs\004"
    "fneg\006fnmadd\007fnmadds\006fnmsub\007fnmsubs\003fre\004fres\004frim\004"
    "frin\004frip\004friz\004frsp\007frsqrte\010frsqrtes\004fsel\005fsqrt\006"
    "fsqrts\004fsub\005fsubs\004icbi\004icbt\005iccci\003ici\006inslwi\006in"
    "srdi\006insrwi\004isel\005isync\002la\003lbz\006lbzcix\004lbzu\005lbzux"
    "\004lbzx\002ld\005ldarx\005ldbrx\005ldcix\003ldu\004ldux\003ldx\003lfd\004"
    "lfdu\005lfdux\004lfdx\006lfiwax\006lfiwzx\003lfs\004lfsu\005lfsux\004lf"
    "sx\003lha\004lhau\005lhaux\004lhax\005lhbrx\003lhz\006lhzcix\004lhzu\005"
    "lhzux\004lhzx\002li\003lis\003lmw\004lswi\005lvebx\005lvehx\005lvewx\004"
    "lvsl\004lvsr\003lvx\004lvxl\003lwa\005lwarx\005lwaux\004lwax\005lwbrx\006"
    "lwsync\003lwz\006lwzcix\004lwzu\005lwzux\004lwzx\005lxsdx\006lxvd2x\006"
    "lxvdsx\006lxvw4x\004mbar\004mcrf\005mfamr\005mfasr\005mfbr0\005mfbr1\005"
    "mfbr2\005mfbr3\005mfbr4\005mfbr5\005mfbr6\005mfbr7\006mfcfar\004mfcr\005"
    "mfctr\005mfdar\007mfdbatl\007mfdbatu\006mfdccr\005mfdcr\006mfdear\005mf"
    "dec\006mfdscr\007mfdsisr\005mfesr\004mffs\007mfibatl\007mfibatu\006mfic"
    "cr\004mflr\005mfmsr\006mfocrf\005mfpid\005mfpvr\006mfrtcl\006mfrtcu\006"
    "mfsdr1\tmfspefscr\005mfspr\006mfsprg\007mfsprg0\007mfsprg1\007mfsprg2\007"
    "mfsprg3\007mfsprg4\007mfsprg5\007mfsprg6\007mfsprg7\004mfsr\006mfsrin\006"
    "mfsrr0\006mfsrr1\006mfsrr2\006mfsrr3\004mftb\006mftbhi\005mftbl\006mftb"
    "lo\005mftbu\005mftcr\006mfvscr\005mfxer\002mr\005msync\005mtamr\005mtas"
    "r\005mtbr0\005mtbr1\005mtbr2\005mtbr3\005mtbr4\005mtbr5\005mtbr6\005mtb"
    "r7\006mtcfar\004mtcr\005mtcrf\005mtctr\005mtdar\007mtdbatl\007mtdbatu\006"
    "mtdccr\005mtdcr\006mtdear\005mtdec\006mtdscr\007mtdsisr\005mtesr\006mtf"
    "sb0\006mtfsb1\005mtfsf\007mtibatl\007mtibatu\006mticcr\004mtlr\005mtmsr"
    "\006mtmsrd\006mtocrf\005mtpid\006mtsdr1\tmtspefscr\005mtspr\006mtsprg\007"
    "mtsprg0\007mtsprg1\007mtsprg2\007mtsprg3\007mtsprg4\007mtsprg5\007mtspr"
    "g6\007mtsprg7\004mtsr\006mtsrin\006mtsrr0\006mtsrr1\006mtsrr2\006mtsrr3"
    "\006mttbhi\005mttbl\006mttblo\005mttbu\005mttcr\006mtvscr\005mtxer\005m"
    "ulhd\006mulhdu\005mulhw\006mulhwu\005mulld\005mulli\005mullw\004nand\003"
    "neg\003nop\003nor\003not\002or\003orc\003ori\004oris\007popcntd\007popc"
    "ntw\007ptesync\004rfci\004rfdi\003rfi\004rfid\005rfmci\005rldcl\005rldc"
    "r\005rldic\006rldicl\006rldicr\006rldimi\006rlwimi\006rlwinm\005rlwnm\005"
    "rotld\006rotldi\005rotlw\006rotlwi\006rotrdi\006rotrwi\002sc\005slbia\005"
    "slbie\007slbmfee\006slbmte\003sld\004sldi\003slw\004slwi\004srad\005sra"
    "di\004sraw\005srawi\003srd\004srdi\003srw\004srwi\003stb\006stbcix\004s"
    "tbu\005stbux\004stbx\003std\006stdbrx\006stdcix\005stdcx\004stdu\005std"
    "ux\004stdx\004stfd\005stfdu\006stfdux\005stfdx\006stfiwx\004stfs\005stf"
    "su\006stfsux\005stfsx\003sth\006sthbrx\006sthcix\004sthu\005sthux\004st"
    "hx\004stmw\005stswi\006stvebx\006stvehx\006stvewx\004stvx\005stvxl\003s"
    "tw\006stwbrx\006stwcix\005stwcx\004stwu\005stwux\004stwx\006stxsdx\007s"
    "txvd2x\007stxvw4x\003sub\004subc\004subf\005subfc\005subfe\006subfic\006"
    "subfme\006subfze\004subi\005subic\005subis\004sync\002td\004tdeq\005tde"
    "qi\004tdge\005tdgei\004tdgt\005tdgti\003tdi\004tdle\005tdlei\005tdlge\006"
    "tdlgei\005tdlgt\006tdlgti\005tdlle\006tdllei\005tdllt\006tdllti\005tdln"
    "g\006tdlngi\005tdlnl\006tdlnli\004tdlt\005tdlti\004tdne\005tdnei\004tdn"
    "g\005tdngi\004tdnl\005tdnli\003tdu\004tdui\005tlbia\005tlbie\006tlbiel\007"
    "tlbivax\005tlbld\005tlbli\005tlbre\007tlbrehi\007tlbrelo\005tlbsx\007tl"
    "bsync\005tlbwe\007tlbwehi\007tlbwelo\004trap\002tw\004tweq\005tweqi\004"
    "twge\005twgei\004twgt\005twgti\003twi\004twle\005twlei\005twlge\006twlg"
    "ei\005twlgt\006twlgti\005twlle\006twllei\005twllt\006twllti\005twlng\006"
    "twlngi\005twlnl\006twlnli\004twlt\005twlti\004twne\005twnei\004twng\005"
    "twngi\004twnl\005twnli\003twu\004twui\007vaddcuw\006vaddfp\007vaddsbs\007"
    "vaddshs\007vaddsws\007vaddubm\007vaddubs\007vadduhm\007vadduhs\007vaddu"
    "wm\007vadduws\004vand\005vandc\006vavgsb\006vavgsh\006vavgsw\006vavgub\006"
    "vavguh\006vavguw\005vcfsx\005vcfux\007vcmpbfp\010vcmpeqfp\010vcmpequb\010"
    "vcmpequh\010vcmpequw\010vcmpgefp\010vcmpgtfp\010vcmpgtsb\010vcmpgtsh\010"
    "vcmpgtsw\010vcmpgtub\010vcmpgtuh\010vcmpgtuw\006vctsxs\006vctuxs\010vex"
    "ptefp\007vlogefp\007vmaddfp\006vmaxfp\006vmaxsb\006vmaxsh\006vmaxsw\006"
    "vmaxub\006vmaxuh\006vmaxuw\tvmhaddshs\nvmhraddshs\006vminfp\006vminsb\006"
    "vminsh\006vminsw\006vminub\006vminuh\006vminuw\tvmladduhm\006vmrghb\006"
    "vmrghh\006vmrghw\006vmrglb\006vmrglh\006vmrglw\010vmsummbm\010vmsumshm\010"
    "vmsumshs\010vmsumubm\010vmsumuhm\010vmsumuhs\007vmulesb\007vmulesh\007v"
    "muleub\007vmuleuh\007vmulosb\007vmulosh\007vmuloub\007vmulouh\010vnmsub"
    "fp\004vnor\003vor\005vperm\005vpkpx\007vpkshss\007vpkshus\007vpkswss\007"
    "vpkswus\007vpkuhum\007vpkuhus\007vpkuwum\007vpkuwus\005vrefp\005vrfim\005"
    "vrfin\005vrfip\005vrfiz\004vrlb\004vrlh\004vrlw\tvrsqrtefp\004vsel\003v"
    "sl\004vslb\006vsldoi\004vslh\004vslo\004vslw\006vspltb\006vsplth\010vsp"
    "ltisb\010vspltish\010vspltisw\006vspltw\003vsr\005vsrab\005vsrah\005vsr"
    "aw\004vsrb\004vsrh\004vsro\004vsrw\007vsubcuw\006vsubfp\007vsubsbs\007v"
    "subshs\007vsubsws\007vsububm\007vsububs\007vsubuhm\007vsubuhs\007vsubuw"
    "m\007vsubuws\010vsum2sws\010vsum4sbs\010vsum4shs\010vsum4ubs\007vsumsws"
    "\007vupkhpx\007vupkhsb\007vupkhsh\007vupklpx\007vupklsb\007vupklsh\004v"
    "xor\004wait\010waitimpl\007waitrsv\005wrtee\006wrteei\004xnop\003xor\004"
    "xori\005xoris\007xsabsdp\007xsadddp\010xscmpodp\010xscmpudp\txscpsgndp\010"
    "xscvdpsp\nxscvdpsxds\nxscvdpsxws\nxscvdpuxds\nxscvdpuxws\010xscvspdp\tx"
    "scvsxddp\txscvuxddp\007xsdivdp\txsmaddadp\txsmaddmdp\007xsmaxdp\007xsmi"
    "ndp\txsmsubadp\txsmsubmdp\007xsmuldp\010xsnabsdp\007xsnegdp\nxsnmaddadp"
    "\nxsnmaddmdp\nxsnmsubadp\nxsnmsubmdp\006xsrdpi\007xsrdpic\007xsrdpim\007"
    "xsrdpip\007xsrdpiz\006xsredp\nxsrsqrtedp\010xssqrtdp\007xssubdp\010xstd"
    "ivdp\txstsqrtdp\007xvabsdp\007xvabssp\007xvadddp\007xvaddsp\txvcmpeqdp\t"
    "xvcmpeqsp\txvcmpgedp\txvcmpgesp\txvcmpgtdp\txvcmpgtsp\txvcpsgndp\txvcps"
    "gnsp\010xvcvdpsp\nxvcvdpsxds\nxvcvdpsxws\nxvcvdpuxds\nxvcvdpuxws\010xvc"
    "vspdp\nxvcvspsxds\nxvcvspsxws\nxvcvspuxds\nxvcvspuxws\txvcvsxddp\txvcvs"
    "xdsp\txvcvsxwdp\txvcvsxwsp\txvcvuxddp\txvcvuxdsp\txvcvuxwdp\txvcvuxwsp\007"
    "xvdivdp\007xvdivsp\txvmaddadp\txvmaddasp\txvmaddmdp\txvmaddmsp\007xvmax"
    "dp\007xvmaxsp\007xvmindp\007xvminsp\007xvmovdp\007xvmovsp\txvmsubadp\tx"
    "vmsubasp\txvmsubmdp\txvmsubmsp\007xvmuldp\007xvmulsp\010xvnabsdp\010xvn"
    "abssp\007xvnegdp\007xvnegsp\nxvnmaddadp\nxvnmaddasp\nxvnmaddmdp\nxvnmad"
    "dmsp\nxvnmsubadp\nxvnmsubasp\nxvnmsubmdp\nxvnmsubmsp\006xvrdpi\007xvrdp"
    "ic\007xvrdpim\007xvrdpip\007xvrdpiz\006xvredp\006xvresp\006xvrspi\007xv"
    "rspic\007xvrspim\007xvrspip\007xvrspiz\nxvrsqrtedp\nxvrsqrtesp\010xvsqr"
    "tdp\010xvsqrtsp\007xvsubdp\007xvsubsp\010xvtdivdp\010xvtdivsp\txvtsqrtd"
    "p\txvtsqrtsp\006xxland\007xxlandc\006xxlnor\005xxlor\006xxlxor\007xxmrg"
    "hd\007xxmrghw\007xxmrgld\007xxmrglw\010xxpermdi\005xxsel\007xxsldwi\007"
    "xxspltd\007xxspltw\007xxswapd";

namespace {
  struct MatchEntry {
    uint16_t Mnemonic;
    uint16_t Opcode;
    uint16_t ConvertFn;
    uint8_t RequiredFeatures;
    uint8_t Classes[6];
    StringRef getMnemonic() const {
      return StringRef(MnemonicTable + Mnemonic + 1,
                       MnemonicTable[Mnemonic]);
    }
  };

  // Predicate for searching for an opcode.
  struct LessOpcode {
    bool operator()(const MatchEntry &LHS, StringRef RHS) {
      return LHS.getMnemonic() < RHS;
    }
    bool operator()(StringRef LHS, const MatchEntry &RHS) {
      return LHS < RHS.getMnemonic();
    }
    bool operator()(const MatchEntry &LHS, const MatchEntry &RHS) {
      return LHS.getMnemonic() < RHS.getMnemonic();
    }
  };
} // end anonymous namespace.

static const MatchEntry MatchTable0[] = {
  { 0 /* add */, PPC::ADD8TLS_, Convert__RegG8RC1_0__RegG8RC1_1__TLSReg1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_TLSReg }, },
  { 0 /* add */, PPC::ADD4, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 0 /* add */, PPC::ADD4o, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4 /* addc */, PPC::ADDC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4 /* addc */, PPC::ADDCo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 9 /* adde */, PPC::ADDE, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 9 /* adde */, PPC::ADDEo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 14 /* addi */, PPC::ADDI, Convert__RegGPRC1_0__RegGPRCNoR01_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRCNoR0, MCK_S16Imm }, },
  { 19 /* addic */, PPC::ADDIC, Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 19 /* addic */, PPC::ADDICo, Convert__RegGPRC1_1__RegGPRC1_2__S16Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 25 /* addis */, PPC::ADDIS, Convert__RegGPRC1_0__RegGPRCNoR01_1__S17Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRCNoR0, MCK_S17Imm }, },
  { 31 /* addme */, PPC::ADDME, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 31 /* addme */, PPC::ADDMEo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 37 /* addze */, PPC::ADDZE, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 37 /* addze */, PPC::ADDZEo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 43 /* and */, PPC::AND, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 43 /* and */, PPC::ANDo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 47 /* andc */, PPC::ANDC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 47 /* andc */, PPC::ANDCo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 52 /* andi */, PPC::ANDIo, Convert__RegGPRC1_1__RegGPRC1_2__U16Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 57 /* andis */, PPC::ANDISo, Convert__RegGPRC1_1__RegGPRC1_2__U16Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 63 /* attn */, PPC::ATTN, Convert_NoOperands, 0, {  }, },
  { 68 /* b */, PPC::B, Convert__DirectBr1_0, 0, { MCK_DirectBr }, },
  { 70 /* ba */, PPC::BA, Convert__DirectBr1_0, 0, { MCK_DirectBr }, },
  { 73 /* bc */, PPC::gBC, Convert__U5Imm1_0__RegCRBITRC1_1__CondBr1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_CondBr }, },
  { 76 /* bca */, PPC::gBCA, Convert__U5Imm1_0__RegCRBITRC1_1__CondBr1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_CondBr }, },
  { 80 /* bcctr */, PPC::gBCCTR, Convert__U5Imm1_0__RegCRBITRC1_1__imm_0, 0, { MCK_U5Imm, MCK_RegCRBITRC }, },
  { 80 /* bcctr */, PPC::gBCCTR, Convert__U5Imm1_0__RegCRBITRC1_1__Imm1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_Imm }, },
  { 86 /* bcctrl */, PPC::gBCCTRL, Convert__U5Imm1_0__RegCRBITRC1_1__imm_0, 0, { MCK_U5Imm, MCK_RegCRBITRC }, },
  { 86 /* bcctrl */, PPC::gBCCTRL, Convert__U5Imm1_0__RegCRBITRC1_1__Imm1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_Imm }, },
  { 93 /* bcl */, PPC::gBCL, Convert__U5Imm1_0__RegCRBITRC1_1__CondBr1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_CondBr }, },
  { 97 /* bcla */, PPC::gBCLA, Convert__U5Imm1_0__RegCRBITRC1_1__CondBr1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_CondBr }, },
  { 102 /* bclr */, PPC::gBCLR, Convert__U5Imm1_0__RegCRBITRC1_1__imm_0, 0, { MCK_U5Imm, MCK_RegCRBITRC }, },
  { 102 /* bclr */, PPC::gBCLR, Convert__U5Imm1_0__RegCRBITRC1_1__Imm1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_Imm }, },
  { 107 /* bclrl */, PPC::gBCLRL, Convert__U5Imm1_0__RegCRBITRC1_1__imm_0, 0, { MCK_U5Imm, MCK_RegCRBITRC }, },
  { 107 /* bclrl */, PPC::gBCLRL, Convert__U5Imm1_0__RegCRBITRC1_1__Imm1_2, 0, { MCK_U5Imm, MCK_RegCRBITRC, MCK_Imm }, },
  { 113 /* bctr */, PPC::BCTR, Convert_NoOperands, 0, {  }, },
  { 118 /* bctrl */, PPC::BCTRL, Convert_NoOperands, 0, {  }, },
  { 124 /* bdnz */, PPC::BDNZ, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 129 /* bdnz+ */, PPC::BDNZp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 135 /* bdnz- */, PPC::BDNZm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 141 /* bdnza */, PPC::BDNZA, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 147 /* bdnza+ */, PPC::BDNZAp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 154 /* bdnza- */, PPC::BDNZAm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 161 /* bdnzf */, PPC::gBC, Convert__imm_0__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 167 /* bdnzfa */, PPC::gBCA, Convert__imm_0__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 174 /* bdnzfl */, PPC::gBCL, Convert__imm_0__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 181 /* bdnzfla */, PPC::gBCLA, Convert__imm_0__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 189 /* bdnzflr */, PPC::gBCLR, Convert__imm_0__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 197 /* bdnzflrl */, PPC::gBCLRL, Convert__imm_0__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 206 /* bdnzl */, PPC::BDNZL, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 212 /* bdnzl+ */, PPC::BDNZLp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 219 /* bdnzl- */, PPC::BDNZLm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 226 /* bdnzla */, PPC::BDNZLA, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 233 /* bdnzla+ */, PPC::BDNZLAp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 241 /* bdnzla- */, PPC::BDNZLAm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 249 /* bdnzlr */, PPC::BDNZLR, Convert_NoOperands, 0, {  }, },
  { 256 /* bdnzlr+ */, PPC::BDNZLRp, Convert_NoOperands, 0, {  }, },
  { 264 /* bdnzlr- */, PPC::BDNZLRm, Convert_NoOperands, 0, {  }, },
  { 272 /* bdnzlrl */, PPC::BDNZLRL, Convert_NoOperands, 0, {  }, },
  { 280 /* bdnzlrl+ */, PPC::BDNZLRLp, Convert_NoOperands, 0, {  }, },
  { 289 /* bdnzlrl- */, PPC::BDNZLRLm, Convert_NoOperands, 0, {  }, },
  { 298 /* bdnzt */, PPC::gBC, Convert__imm_8__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 304 /* bdnzta */, PPC::gBCA, Convert__imm_8__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 311 /* bdnztl */, PPC::gBCL, Convert__imm_8__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 318 /* bdnztla */, PPC::gBCLA, Convert__imm_8__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 326 /* bdnztlr */, PPC::gBCLR, Convert__imm_8__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 334 /* bdnztlrl */, PPC::gBCLRL, Convert__imm_8__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 343 /* bdz */, PPC::BDZ, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 347 /* bdz+ */, PPC::BDZp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 352 /* bdz- */, PPC::BDZm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 357 /* bdza */, PPC::BDZA, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 362 /* bdza+ */, PPC::BDZAp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 368 /* bdza- */, PPC::BDZAm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 374 /* bdzf */, PPC::gBC, Convert__imm_2__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 379 /* bdzfa */, PPC::gBCA, Convert__imm_2__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 385 /* bdzfl */, PPC::gBCL, Convert__imm_2__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 391 /* bdzfla */, PPC::gBCLA, Convert__imm_2__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 398 /* bdzflr */, PPC::gBCLR, Convert__imm_2__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 405 /* bdzflrl */, PPC::gBCLRL, Convert__imm_2__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 413 /* bdzl */, PPC::BDZL, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 418 /* bdzl+ */, PPC::BDZLp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 424 /* bdzl- */, PPC::BDZLm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 430 /* bdzla */, PPC::BDZLA, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 436 /* bdzla+ */, PPC::BDZLAp, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 443 /* bdzla- */, PPC::BDZLAm, Convert__CondBr1_0, 0, { MCK_CondBr }, },
  { 450 /* bdzlr */, PPC::BDZLR, Convert_NoOperands, 0, {  }, },
  { 456 /* bdzlr+ */, PPC::BDZLRp, Convert_NoOperands, 0, {  }, },
  { 463 /* bdzlr- */, PPC::BDZLRm, Convert_NoOperands, 0, {  }, },
  { 470 /* bdzlrl */, PPC::BDZLRL, Convert_NoOperands, 0, {  }, },
  { 477 /* bdzlrl+ */, PPC::BDZLRLp, Convert_NoOperands, 0, {  }, },
  { 485 /* bdzlrl- */, PPC::BDZLRLm, Convert_NoOperands, 0, {  }, },
  { 493 /* bdzt */, PPC::gBC, Convert__imm_10__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 498 /* bdzta */, PPC::gBCA, Convert__imm_10__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 504 /* bdztl */, PPC::gBCL, Convert__imm_10__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 510 /* bdztla */, PPC::gBCLA, Convert__imm_10__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 517 /* bdztlr */, PPC::gBCLR, Convert__imm_10__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 524 /* bdztlrl */, PPC::gBCLRL, Convert__imm_10__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 532 /* beq */, PPC::BCC, Convert__imm_76__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 532 /* beq */, PPC::BCC, Convert__imm_76__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 536 /* beq+ */, PPC::BCC, Convert__imm_79__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 536 /* beq+ */, PPC::BCC, Convert__imm_79__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 541 /* beq- */, PPC::BCC, Convert__imm_78__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 541 /* beq- */, PPC::BCC, Convert__imm_78__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 546 /* beqa */, PPC::BCCA, Convert__imm_76__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 546 /* beqa */, PPC::BCCA, Convert__imm_76__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 551 /* beqa+ */, PPC::BCCA, Convert__imm_79__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 551 /* beqa+ */, PPC::BCCA, Convert__imm_79__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 557 /* beqa- */, PPC::BCCA, Convert__imm_78__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 557 /* beqa- */, PPC::BCCA, Convert__imm_78__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 563 /* beqctr */, PPC::BCCCTR, Convert__imm_76__regCR0, 0, {  }, },
  { 563 /* beqctr */, PPC::BCCCTR, Convert__imm_76__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 570 /* beqctr+ */, PPC::BCCCTR, Convert__imm_79__regCR0, 0, {  }, },
  { 570 /* beqctr+ */, PPC::BCCCTR, Convert__imm_79__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 578 /* beqctr- */, PPC::BCCCTR, Convert__imm_78__regCR0, 0, {  }, },
  { 578 /* beqctr- */, PPC::BCCCTR, Convert__imm_78__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 586 /* beqctrl */, PPC::BCCCTRL, Convert__imm_76__regCR0, 0, {  }, },
  { 586 /* beqctrl */, PPC::BCCCTRL, Convert__imm_76__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 594 /* beqctrl+ */, PPC::BCCCTRL, Convert__imm_79__regCR0, 0, {  }, },
  { 594 /* beqctrl+ */, PPC::BCCCTRL, Convert__imm_79__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 603 /* beqctrl- */, PPC::BCCCTRL, Convert__imm_78__regCR0, 0, {  }, },
  { 603 /* beqctrl- */, PPC::BCCCTRL, Convert__imm_78__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 612 /* beql */, PPC::BCCL, Convert__imm_76__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 612 /* beql */, PPC::BCCL, Convert__imm_76__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 617 /* beql+ */, PPC::BCCL, Convert__imm_79__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 617 /* beql+ */, PPC::BCCL, Convert__imm_79__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 623 /* beql- */, PPC::BCCL, Convert__imm_78__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 623 /* beql- */, PPC::BCCL, Convert__imm_78__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 629 /* beqla */, PPC::BCCLA, Convert__imm_76__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 629 /* beqla */, PPC::BCCLA, Convert__imm_76__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 635 /* beqla+ */, PPC::BCCLA, Convert__imm_79__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 635 /* beqla+ */, PPC::BCCLA, Convert__imm_79__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 642 /* beqla- */, PPC::BCCLA, Convert__imm_78__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 642 /* beqla- */, PPC::BCCLA, Convert__imm_78__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 649 /* beqlr */, PPC::BCCLR, Convert__imm_76__regCR0, 0, {  }, },
  { 649 /* beqlr */, PPC::BCCLR, Convert__imm_76__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 655 /* beqlr+ */, PPC::BCCLR, Convert__imm_79__regCR0, 0, {  }, },
  { 655 /* beqlr+ */, PPC::BCCLR, Convert__imm_79__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 662 /* beqlr- */, PPC::BCCLR, Convert__imm_78__regCR0, 0, {  }, },
  { 662 /* beqlr- */, PPC::BCCLR, Convert__imm_78__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 669 /* beqlrl */, PPC::BCCLRL, Convert__imm_76__regCR0, 0, {  }, },
  { 669 /* beqlrl */, PPC::BCCLRL, Convert__imm_76__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 676 /* beqlrl+ */, PPC::BCCLRL, Convert__imm_79__regCR0, 0, {  }, },
  { 676 /* beqlrl+ */, PPC::BCCLRL, Convert__imm_79__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 684 /* beqlrl- */, PPC::BCCLRL, Convert__imm_78__regCR0, 0, {  }, },
  { 684 /* beqlrl- */, PPC::BCCLRL, Convert__imm_78__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 692 /* bf */, PPC::gBC, Convert__imm_4__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 695 /* bf+ */, PPC::gBC, Convert__imm_7__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 699 /* bf- */, PPC::gBC, Convert__imm_6__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 703 /* bfa */, PPC::gBCA, Convert__imm_4__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 707 /* bfa+ */, PPC::gBCA, Convert__imm_7__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 712 /* bfa- */, PPC::gBCA, Convert__imm_6__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 717 /* bfctr */, PPC::gBCCTR, Convert__imm_4__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 723 /* bfctr+ */, PPC::gBCCTR, Convert__imm_7__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 730 /* bfctr- */, PPC::gBCCTR, Convert__imm_6__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 737 /* bfctrl */, PPC::gBCCTRL, Convert__imm_4__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 744 /* bfctrl+ */, PPC::gBCCTRL, Convert__imm_7__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 752 /* bfctrl- */, PPC::gBCCTRL, Convert__imm_6__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 760 /* bfl */, PPC::gBCL, Convert__imm_4__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 764 /* bfl+ */, PPC::gBCL, Convert__imm_7__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 769 /* bfl- */, PPC::gBCL, Convert__imm_6__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 774 /* bfla */, PPC::gBCLA, Convert__imm_4__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 779 /* bfla+ */, PPC::gBCLA, Convert__imm_7__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 785 /* bfla- */, PPC::gBCLA, Convert__imm_6__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 791 /* bflr */, PPC::gBCLR, Convert__imm_4__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 796 /* bflr+ */, PPC::gBCLR, Convert__imm_7__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 802 /* bflr- */, PPC::gBCLR, Convert__imm_6__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 808 /* bflrl */, PPC::gBCLRL, Convert__imm_4__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 814 /* bflrl+ */, PPC::gBCLRL, Convert__imm_7__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 821 /* bflrl- */, PPC::gBCLRL, Convert__imm_6__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 828 /* bge */, PPC::BCC, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 828 /* bge */, PPC::BCC, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 832 /* bge+ */, PPC::BCC, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 832 /* bge+ */, PPC::BCC, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 837 /* bge- */, PPC::BCC, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 837 /* bge- */, PPC::BCC, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 842 /* bgea */, PPC::BCCA, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 842 /* bgea */, PPC::BCCA, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 847 /* bgea+ */, PPC::BCCA, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 847 /* bgea+ */, PPC::BCCA, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 853 /* bgea- */, PPC::BCCA, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 853 /* bgea- */, PPC::BCCA, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 859 /* bgectr */, PPC::BCCCTR, Convert__imm_4__regCR0, 0, {  }, },
  { 859 /* bgectr */, PPC::BCCCTR, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 866 /* bgectr+ */, PPC::BCCCTR, Convert__imm_7__regCR0, 0, {  }, },
  { 866 /* bgectr+ */, PPC::BCCCTR, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 874 /* bgectr- */, PPC::BCCCTR, Convert__imm_6__regCR0, 0, {  }, },
  { 874 /* bgectr- */, PPC::BCCCTR, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 882 /* bgectrl */, PPC::BCCCTRL, Convert__imm_4__regCR0, 0, {  }, },
  { 882 /* bgectrl */, PPC::BCCCTRL, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 890 /* bgectrl+ */, PPC::BCCCTRL, Convert__imm_7__regCR0, 0, {  }, },
  { 890 /* bgectrl+ */, PPC::BCCCTRL, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 899 /* bgectrl- */, PPC::BCCCTRL, Convert__imm_6__regCR0, 0, {  }, },
  { 899 /* bgectrl- */, PPC::BCCCTRL, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 908 /* bgel */, PPC::BCCL, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 908 /* bgel */, PPC::BCCL, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 913 /* bgel+ */, PPC::BCCL, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 913 /* bgel+ */, PPC::BCCL, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 919 /* bgel- */, PPC::BCCL, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 919 /* bgel- */, PPC::BCCL, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 925 /* bgela */, PPC::BCCLA, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 925 /* bgela */, PPC::BCCLA, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 931 /* bgela+ */, PPC::BCCLA, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 931 /* bgela+ */, PPC::BCCLA, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 938 /* bgela- */, PPC::BCCLA, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 938 /* bgela- */, PPC::BCCLA, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 945 /* bgelr */, PPC::BCCLR, Convert__imm_4__regCR0, 0, {  }, },
  { 945 /* bgelr */, PPC::BCCLR, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 951 /* bgelr+ */, PPC::BCCLR, Convert__imm_7__regCR0, 0, {  }, },
  { 951 /* bgelr+ */, PPC::BCCLR, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 958 /* bgelr- */, PPC::BCCLR, Convert__imm_6__regCR0, 0, {  }, },
  { 958 /* bgelr- */, PPC::BCCLR, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 965 /* bgelrl */, PPC::BCCLRL, Convert__imm_4__regCR0, 0, {  }, },
  { 965 /* bgelrl */, PPC::BCCLRL, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 972 /* bgelrl+ */, PPC::BCCLRL, Convert__imm_7__regCR0, 0, {  }, },
  { 972 /* bgelrl+ */, PPC::BCCLRL, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 980 /* bgelrl- */, PPC::BCCLRL, Convert__imm_6__regCR0, 0, {  }, },
  { 980 /* bgelrl- */, PPC::BCCLRL, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 988 /* bgt */, PPC::BCC, Convert__imm_44__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 988 /* bgt */, PPC::BCC, Convert__imm_44__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 992 /* bgt+ */, PPC::BCC, Convert__imm_47__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 992 /* bgt+ */, PPC::BCC, Convert__imm_47__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 997 /* bgt- */, PPC::BCC, Convert__imm_46__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 997 /* bgt- */, PPC::BCC, Convert__imm_46__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1002 /* bgta */, PPC::BCCA, Convert__imm_44__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1002 /* bgta */, PPC::BCCA, Convert__imm_44__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1007 /* bgta+ */, PPC::BCCA, Convert__imm_47__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1007 /* bgta+ */, PPC::BCCA, Convert__imm_47__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1013 /* bgta- */, PPC::BCCA, Convert__imm_46__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1013 /* bgta- */, PPC::BCCA, Convert__imm_46__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1019 /* bgtctr */, PPC::BCCCTR, Convert__imm_44__regCR0, 0, {  }, },
  { 1019 /* bgtctr */, PPC::BCCCTR, Convert__imm_44__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1026 /* bgtctr+ */, PPC::BCCCTR, Convert__imm_47__regCR0, 0, {  }, },
  { 1026 /* bgtctr+ */, PPC::BCCCTR, Convert__imm_47__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1034 /* bgtctr- */, PPC::BCCCTR, Convert__imm_46__regCR0, 0, {  }, },
  { 1034 /* bgtctr- */, PPC::BCCCTR, Convert__imm_46__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1042 /* bgtctrl */, PPC::BCCCTRL, Convert__imm_44__regCR0, 0, {  }, },
  { 1042 /* bgtctrl */, PPC::BCCCTRL, Convert__imm_44__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1050 /* bgtctrl+ */, PPC::BCCCTRL, Convert__imm_47__regCR0, 0, {  }, },
  { 1050 /* bgtctrl+ */, PPC::BCCCTRL, Convert__imm_47__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1059 /* bgtctrl- */, PPC::BCCCTRL, Convert__imm_46__regCR0, 0, {  }, },
  { 1059 /* bgtctrl- */, PPC::BCCCTRL, Convert__imm_46__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1068 /* bgtl */, PPC::BCCL, Convert__imm_44__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1068 /* bgtl */, PPC::BCCL, Convert__imm_44__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1073 /* bgtl+ */, PPC::BCCL, Convert__imm_47__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1073 /* bgtl+ */, PPC::BCCL, Convert__imm_47__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1079 /* bgtl- */, PPC::BCCL, Convert__imm_46__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1079 /* bgtl- */, PPC::BCCL, Convert__imm_46__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1085 /* bgtla */, PPC::BCCLA, Convert__imm_44__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1085 /* bgtla */, PPC::BCCLA, Convert__imm_44__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1091 /* bgtla+ */, PPC::BCCLA, Convert__imm_47__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1091 /* bgtla+ */, PPC::BCCLA, Convert__imm_47__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1098 /* bgtla- */, PPC::BCCLA, Convert__imm_46__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1098 /* bgtla- */, PPC::BCCLA, Convert__imm_46__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1105 /* bgtlr */, PPC::BCCLR, Convert__imm_44__regCR0, 0, {  }, },
  { 1105 /* bgtlr */, PPC::BCCLR, Convert__imm_44__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1111 /* bgtlr+ */, PPC::BCCLR, Convert__imm_47__regCR0, 0, {  }, },
  { 1111 /* bgtlr+ */, PPC::BCCLR, Convert__imm_47__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1118 /* bgtlr- */, PPC::BCCLR, Convert__imm_46__regCR0, 0, {  }, },
  { 1118 /* bgtlr- */, PPC::BCCLR, Convert__imm_46__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1125 /* bgtlrl */, PPC::BCCLRL, Convert__imm_44__regCR0, 0, {  }, },
  { 1125 /* bgtlrl */, PPC::BCCLRL, Convert__imm_44__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1132 /* bgtlrl+ */, PPC::BCCLRL, Convert__imm_47__regCR0, 0, {  }, },
  { 1132 /* bgtlrl+ */, PPC::BCCLRL, Convert__imm_47__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1140 /* bgtlrl- */, PPC::BCCLRL, Convert__imm_46__regCR0, 0, {  }, },
  { 1140 /* bgtlrl- */, PPC::BCCLRL, Convert__imm_46__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1148 /* bl */, PPC::BL, Convert__DirectBr1_0, 0, { MCK_DirectBr }, },
  { 1148 /* bl */, PPC::BL8_TLS_, Convert__DirectBr1_0__Imm1_1, 0, { MCK_DirectBr, MCK_Imm }, },
  { 1151 /* bla */, PPC::BLA, Convert__DirectBr1_0, 0, { MCK_DirectBr }, },
  { 1155 /* ble */, PPC::BCC, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1155 /* ble */, PPC::BCC, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1159 /* ble+ */, PPC::BCC, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1159 /* ble+ */, PPC::BCC, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1164 /* ble- */, PPC::BCC, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1164 /* ble- */, PPC::BCC, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1169 /* blea */, PPC::BCCA, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1169 /* blea */, PPC::BCCA, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1174 /* blea+ */, PPC::BCCA, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1174 /* blea+ */, PPC::BCCA, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1180 /* blea- */, PPC::BCCA, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1180 /* blea- */, PPC::BCCA, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1186 /* blectr */, PPC::BCCCTR, Convert__imm_36__regCR0, 0, {  }, },
  { 1186 /* blectr */, PPC::BCCCTR, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1193 /* blectr+ */, PPC::BCCCTR, Convert__imm_39__regCR0, 0, {  }, },
  { 1193 /* blectr+ */, PPC::BCCCTR, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1201 /* blectr- */, PPC::BCCCTR, Convert__imm_38__regCR0, 0, {  }, },
  { 1201 /* blectr- */, PPC::BCCCTR, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1209 /* blectrl */, PPC::BCCCTRL, Convert__imm_36__regCR0, 0, {  }, },
  { 1209 /* blectrl */, PPC::BCCCTRL, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1217 /* blectrl+ */, PPC::BCCCTRL, Convert__imm_39__regCR0, 0, {  }, },
  { 1217 /* blectrl+ */, PPC::BCCCTRL, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1226 /* blectrl- */, PPC::BCCCTRL, Convert__imm_38__regCR0, 0, {  }, },
  { 1226 /* blectrl- */, PPC::BCCCTRL, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1235 /* blel */, PPC::BCCL, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1235 /* blel */, PPC::BCCL, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1240 /* blel+ */, PPC::BCCL, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1240 /* blel+ */, PPC::BCCL, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1246 /* blel- */, PPC::BCCL, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1246 /* blel- */, PPC::BCCL, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1252 /* blela */, PPC::BCCLA, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1252 /* blela */, PPC::BCCLA, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1258 /* blela+ */, PPC::BCCLA, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1258 /* blela+ */, PPC::BCCLA, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1265 /* blela- */, PPC::BCCLA, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1265 /* blela- */, PPC::BCCLA, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1272 /* blelr */, PPC::BCCLR, Convert__imm_36__regCR0, 0, {  }, },
  { 1272 /* blelr */, PPC::BCCLR, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1278 /* blelr+ */, PPC::BCCLR, Convert__imm_39__regCR0, 0, {  }, },
  { 1278 /* blelr+ */, PPC::BCCLR, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1285 /* blelr- */, PPC::BCCLR, Convert__imm_38__regCR0, 0, {  }, },
  { 1285 /* blelr- */, PPC::BCCLR, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1292 /* blelrl */, PPC::BCCLRL, Convert__imm_36__regCR0, 0, {  }, },
  { 1292 /* blelrl */, PPC::BCCLRL, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1299 /* blelrl+ */, PPC::BCCLRL, Convert__imm_39__regCR0, 0, {  }, },
  { 1299 /* blelrl+ */, PPC::BCCLRL, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1307 /* blelrl- */, PPC::BCCLRL, Convert__imm_38__regCR0, 0, {  }, },
  { 1307 /* blelrl- */, PPC::BCCLRL, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1315 /* blr */, PPC::BLR, Convert_NoOperands, 0, {  }, },
  { 1319 /* blrl */, PPC::BLRL, Convert_NoOperands, 0, {  }, },
  { 1324 /* blt */, PPC::BCC, Convert__imm_12__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1324 /* blt */, PPC::BCC, Convert__imm_12__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1328 /* blt+ */, PPC::BCC, Convert__imm_15__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1328 /* blt+ */, PPC::BCC, Convert__imm_15__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1333 /* blt- */, PPC::BCC, Convert__imm_14__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1333 /* blt- */, PPC::BCC, Convert__imm_14__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1338 /* blta */, PPC::BCCA, Convert__imm_12__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1338 /* blta */, PPC::BCCA, Convert__imm_12__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1343 /* blta+ */, PPC::BCCA, Convert__imm_15__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1343 /* blta+ */, PPC::BCCA, Convert__imm_15__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1349 /* blta- */, PPC::BCCA, Convert__imm_14__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1349 /* blta- */, PPC::BCCA, Convert__imm_14__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1355 /* bltctr */, PPC::BCCCTR, Convert__imm_12__regCR0, 0, {  }, },
  { 1355 /* bltctr */, PPC::BCCCTR, Convert__imm_12__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1362 /* bltctr+ */, PPC::BCCCTR, Convert__imm_15__regCR0, 0, {  }, },
  { 1362 /* bltctr+ */, PPC::BCCCTR, Convert__imm_15__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1370 /* bltctr- */, PPC::BCCCTR, Convert__imm_14__regCR0, 0, {  }, },
  { 1370 /* bltctr- */, PPC::BCCCTR, Convert__imm_14__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1378 /* bltctrl */, PPC::BCCCTRL, Convert__imm_12__regCR0, 0, {  }, },
  { 1378 /* bltctrl */, PPC::BCCCTRL, Convert__imm_12__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1386 /* bltctrl+ */, PPC::BCCCTRL, Convert__imm_15__regCR0, 0, {  }, },
  { 1386 /* bltctrl+ */, PPC::BCCCTRL, Convert__imm_15__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1395 /* bltctrl- */, PPC::BCCCTRL, Convert__imm_14__regCR0, 0, {  }, },
  { 1395 /* bltctrl- */, PPC::BCCCTRL, Convert__imm_14__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1404 /* bltl */, PPC::BCCL, Convert__imm_12__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1404 /* bltl */, PPC::BCCL, Convert__imm_12__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1409 /* bltl+ */, PPC::BCCL, Convert__imm_15__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1409 /* bltl+ */, PPC::BCCL, Convert__imm_15__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1415 /* bltl- */, PPC::BCCL, Convert__imm_14__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1415 /* bltl- */, PPC::BCCL, Convert__imm_14__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1421 /* bltla */, PPC::BCCLA, Convert__imm_12__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1421 /* bltla */, PPC::BCCLA, Convert__imm_12__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1427 /* bltla+ */, PPC::BCCLA, Convert__imm_15__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1427 /* bltla+ */, PPC::BCCLA, Convert__imm_15__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1434 /* bltla- */, PPC::BCCLA, Convert__imm_14__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1434 /* bltla- */, PPC::BCCLA, Convert__imm_14__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1441 /* bltlr */, PPC::BCCLR, Convert__imm_12__regCR0, 0, {  }, },
  { 1441 /* bltlr */, PPC::BCCLR, Convert__imm_12__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1447 /* bltlr+ */, PPC::BCCLR, Convert__imm_15__regCR0, 0, {  }, },
  { 1447 /* bltlr+ */, PPC::BCCLR, Convert__imm_15__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1454 /* bltlr- */, PPC::BCCLR, Convert__imm_14__regCR0, 0, {  }, },
  { 1454 /* bltlr- */, PPC::BCCLR, Convert__imm_14__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1461 /* bltlrl */, PPC::BCCLRL, Convert__imm_12__regCR0, 0, {  }, },
  { 1461 /* bltlrl */, PPC::BCCLRL, Convert__imm_12__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1468 /* bltlrl+ */, PPC::BCCLRL, Convert__imm_15__regCR0, 0, {  }, },
  { 1468 /* bltlrl+ */, PPC::BCCLRL, Convert__imm_15__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1476 /* bltlrl- */, PPC::BCCLRL, Convert__imm_14__regCR0, 0, {  }, },
  { 1476 /* bltlrl- */, PPC::BCCLRL, Convert__imm_14__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1484 /* bne */, PPC::BCC, Convert__imm_68__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1484 /* bne */, PPC::BCC, Convert__imm_68__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1488 /* bne+ */, PPC::BCC, Convert__imm_71__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1488 /* bne+ */, PPC::BCC, Convert__imm_71__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1493 /* bne- */, PPC::BCC, Convert__imm_70__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1493 /* bne- */, PPC::BCC, Convert__imm_70__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1498 /* bnea */, PPC::BCCA, Convert__imm_68__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1498 /* bnea */, PPC::BCCA, Convert__imm_68__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1503 /* bnea+ */, PPC::BCCA, Convert__imm_71__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1503 /* bnea+ */, PPC::BCCA, Convert__imm_71__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1509 /* bnea- */, PPC::BCCA, Convert__imm_70__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1509 /* bnea- */, PPC::BCCA, Convert__imm_70__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1515 /* bnectr */, PPC::BCCCTR, Convert__imm_68__regCR0, 0, {  }, },
  { 1515 /* bnectr */, PPC::BCCCTR, Convert__imm_68__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1522 /* bnectr+ */, PPC::BCCCTR, Convert__imm_71__regCR0, 0, {  }, },
  { 1522 /* bnectr+ */, PPC::BCCCTR, Convert__imm_71__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1530 /* bnectr- */, PPC::BCCCTR, Convert__imm_70__regCR0, 0, {  }, },
  { 1530 /* bnectr- */, PPC::BCCCTR, Convert__imm_70__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1538 /* bnectrl */, PPC::BCCCTRL, Convert__imm_68__regCR0, 0, {  }, },
  { 1538 /* bnectrl */, PPC::BCCCTRL, Convert__imm_68__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1546 /* bnectrl+ */, PPC::BCCCTRL, Convert__imm_71__regCR0, 0, {  }, },
  { 1546 /* bnectrl+ */, PPC::BCCCTRL, Convert__imm_71__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1555 /* bnectrl- */, PPC::BCCCTRL, Convert__imm_70__regCR0, 0, {  }, },
  { 1555 /* bnectrl- */, PPC::BCCCTRL, Convert__imm_70__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1564 /* bnel */, PPC::BCCL, Convert__imm_68__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1564 /* bnel */, PPC::BCCL, Convert__imm_68__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1569 /* bnel+ */, PPC::BCCL, Convert__imm_71__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1569 /* bnel+ */, PPC::BCCL, Convert__imm_71__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1575 /* bnel- */, PPC::BCCL, Convert__imm_70__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1575 /* bnel- */, PPC::BCCL, Convert__imm_70__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1581 /* bnela */, PPC::BCCLA, Convert__imm_68__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1581 /* bnela */, PPC::BCCLA, Convert__imm_68__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1587 /* bnela+ */, PPC::BCCLA, Convert__imm_71__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1587 /* bnela+ */, PPC::BCCLA, Convert__imm_71__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1594 /* bnela- */, PPC::BCCLA, Convert__imm_70__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1594 /* bnela- */, PPC::BCCLA, Convert__imm_70__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1601 /* bnelr */, PPC::BCCLR, Convert__imm_68__regCR0, 0, {  }, },
  { 1601 /* bnelr */, PPC::BCCLR, Convert__imm_68__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1607 /* bnelr+ */, PPC::BCCLR, Convert__imm_71__regCR0, 0, {  }, },
  { 1607 /* bnelr+ */, PPC::BCCLR, Convert__imm_71__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1614 /* bnelr- */, PPC::BCCLR, Convert__imm_70__regCR0, 0, {  }, },
  { 1614 /* bnelr- */, PPC::BCCLR, Convert__imm_70__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1621 /* bnelrl */, PPC::BCCLRL, Convert__imm_68__regCR0, 0, {  }, },
  { 1621 /* bnelrl */, PPC::BCCLRL, Convert__imm_68__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1628 /* bnelrl+ */, PPC::BCCLRL, Convert__imm_71__regCR0, 0, {  }, },
  { 1628 /* bnelrl+ */, PPC::BCCLRL, Convert__imm_71__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1636 /* bnelrl- */, PPC::BCCLRL, Convert__imm_70__regCR0, 0, {  }, },
  { 1636 /* bnelrl- */, PPC::BCCLRL, Convert__imm_70__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1644 /* bng */, PPC::BCC, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1644 /* bng */, PPC::BCC, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1648 /* bng+ */, PPC::BCC, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1648 /* bng+ */, PPC::BCC, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1653 /* bng- */, PPC::BCC, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1653 /* bng- */, PPC::BCC, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1658 /* bnga */, PPC::BCCA, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1658 /* bnga */, PPC::BCCA, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1663 /* bnga+ */, PPC::BCCA, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1663 /* bnga+ */, PPC::BCCA, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1669 /* bnga- */, PPC::BCCA, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1669 /* bnga- */, PPC::BCCA, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1675 /* bngctr */, PPC::BCCCTR, Convert__imm_36__regCR0, 0, {  }, },
  { 1675 /* bngctr */, PPC::BCCCTR, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1682 /* bngctr+ */, PPC::BCCCTR, Convert__imm_39__regCR0, 0, {  }, },
  { 1682 /* bngctr+ */, PPC::BCCCTR, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1690 /* bngctr- */, PPC::BCCCTR, Convert__imm_38__regCR0, 0, {  }, },
  { 1690 /* bngctr- */, PPC::BCCCTR, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1698 /* bngctrl */, PPC::BCCCTRL, Convert__imm_36__regCR0, 0, {  }, },
  { 1698 /* bngctrl */, PPC::BCCCTRL, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1706 /* bngctrl+ */, PPC::BCCCTRL, Convert__imm_39__regCR0, 0, {  }, },
  { 1706 /* bngctrl+ */, PPC::BCCCTRL, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1715 /* bngctrl- */, PPC::BCCCTRL, Convert__imm_38__regCR0, 0, {  }, },
  { 1715 /* bngctrl- */, PPC::BCCCTRL, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1724 /* bngl */, PPC::BCCL, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1724 /* bngl */, PPC::BCCL, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1729 /* bngl+ */, PPC::BCCL, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1729 /* bngl+ */, PPC::BCCL, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1735 /* bngl- */, PPC::BCCL, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1735 /* bngl- */, PPC::BCCL, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1741 /* bngla */, PPC::BCCLA, Convert__imm_36__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1741 /* bngla */, PPC::BCCLA, Convert__imm_36__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1747 /* bngla+ */, PPC::BCCLA, Convert__imm_39__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1747 /* bngla+ */, PPC::BCCLA, Convert__imm_39__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1754 /* bngla- */, PPC::BCCLA, Convert__imm_38__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1754 /* bngla- */, PPC::BCCLA, Convert__imm_38__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1761 /* bnglr */, PPC::BCCLR, Convert__imm_36__regCR0, 0, {  }, },
  { 1761 /* bnglr */, PPC::BCCLR, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1767 /* bnglr+ */, PPC::BCCLR, Convert__imm_39__regCR0, 0, {  }, },
  { 1767 /* bnglr+ */, PPC::BCCLR, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1774 /* bnglr- */, PPC::BCCLR, Convert__imm_38__regCR0, 0, {  }, },
  { 1774 /* bnglr- */, PPC::BCCLR, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1781 /* bnglrl */, PPC::BCCLRL, Convert__imm_36__regCR0, 0, {  }, },
  { 1781 /* bnglrl */, PPC::BCCLRL, Convert__imm_36__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1788 /* bnglrl+ */, PPC::BCCLRL, Convert__imm_39__regCR0, 0, {  }, },
  { 1788 /* bnglrl+ */, PPC::BCCLRL, Convert__imm_39__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1796 /* bnglrl- */, PPC::BCCLRL, Convert__imm_38__regCR0, 0, {  }, },
  { 1796 /* bnglrl- */, PPC::BCCLRL, Convert__imm_38__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1804 /* bnl */, PPC::BCC, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1804 /* bnl */, PPC::BCC, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1808 /* bnl+ */, PPC::BCC, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1808 /* bnl+ */, PPC::BCC, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1813 /* bnl- */, PPC::BCC, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1813 /* bnl- */, PPC::BCC, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1818 /* bnla */, PPC::BCCA, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1818 /* bnla */, PPC::BCCA, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1823 /* bnla+ */, PPC::BCCA, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1823 /* bnla+ */, PPC::BCCA, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1829 /* bnla- */, PPC::BCCA, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1829 /* bnla- */, PPC::BCCA, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1835 /* bnlctr */, PPC::BCCCTR, Convert__imm_4__regCR0, 0, {  }, },
  { 1835 /* bnlctr */, PPC::BCCCTR, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1842 /* bnlctr+ */, PPC::BCCCTR, Convert__imm_7__regCR0, 0, {  }, },
  { 1842 /* bnlctr+ */, PPC::BCCCTR, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1850 /* bnlctr- */, PPC::BCCCTR, Convert__imm_6__regCR0, 0, {  }, },
  { 1850 /* bnlctr- */, PPC::BCCCTR, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1858 /* bnlctrl */, PPC::BCCCTRL, Convert__imm_4__regCR0, 0, {  }, },
  { 1858 /* bnlctrl */, PPC::BCCCTRL, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1866 /* bnlctrl+ */, PPC::BCCCTRL, Convert__imm_7__regCR0, 0, {  }, },
  { 1866 /* bnlctrl+ */, PPC::BCCCTRL, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1875 /* bnlctrl- */, PPC::BCCCTRL, Convert__imm_6__regCR0, 0, {  }, },
  { 1875 /* bnlctrl- */, PPC::BCCCTRL, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1884 /* bnll */, PPC::BCCL, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1884 /* bnll */, PPC::BCCL, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1889 /* bnll+ */, PPC::BCCL, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1889 /* bnll+ */, PPC::BCCL, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1895 /* bnll- */, PPC::BCCL, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1895 /* bnll- */, PPC::BCCL, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1901 /* bnlla */, PPC::BCCLA, Convert__imm_4__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1901 /* bnlla */, PPC::BCCLA, Convert__imm_4__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1907 /* bnlla+ */, PPC::BCCLA, Convert__imm_7__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1907 /* bnlla+ */, PPC::BCCLA, Convert__imm_7__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1914 /* bnlla- */, PPC::BCCLA, Convert__imm_6__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1914 /* bnlla- */, PPC::BCCLA, Convert__imm_6__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1921 /* bnllr */, PPC::BCCLR, Convert__imm_4__regCR0, 0, {  }, },
  { 1921 /* bnllr */, PPC::BCCLR, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1927 /* bnllr+ */, PPC::BCCLR, Convert__imm_7__regCR0, 0, {  }, },
  { 1927 /* bnllr+ */, PPC::BCCLR, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1934 /* bnllr- */, PPC::BCCLR, Convert__imm_6__regCR0, 0, {  }, },
  { 1934 /* bnllr- */, PPC::BCCLR, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1941 /* bnllrl */, PPC::BCCLRL, Convert__imm_4__regCR0, 0, {  }, },
  { 1941 /* bnllrl */, PPC::BCCLRL, Convert__imm_4__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1948 /* bnllrl+ */, PPC::BCCLRL, Convert__imm_7__regCR0, 0, {  }, },
  { 1948 /* bnllrl+ */, PPC::BCCLRL, Convert__imm_7__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1956 /* bnllrl- */, PPC::BCCLRL, Convert__imm_6__regCR0, 0, {  }, },
  { 1956 /* bnllrl- */, PPC::BCCLRL, Convert__imm_6__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 1964 /* bns */, PPC::BCC, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1964 /* bns */, PPC::BCC, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1968 /* bns+ */, PPC::BCC, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1968 /* bns+ */, PPC::BCC, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1973 /* bns- */, PPC::BCC, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1973 /* bns- */, PPC::BCC, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1978 /* bnsa */, PPC::BCCA, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1978 /* bnsa */, PPC::BCCA, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1983 /* bnsa+ */, PPC::BCCA, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1983 /* bnsa+ */, PPC::BCCA, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1989 /* bnsa- */, PPC::BCCA, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 1989 /* bnsa- */, PPC::BCCA, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 1995 /* bnsctr */, PPC::BCCCTR, Convert__imm_100__regCR0, 0, {  }, },
  { 1995 /* bnsctr */, PPC::BCCCTR, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2002 /* bnsctr+ */, PPC::BCCCTR, Convert__imm_103__regCR0, 0, {  }, },
  { 2002 /* bnsctr+ */, PPC::BCCCTR, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2010 /* bnsctr- */, PPC::BCCCTR, Convert__imm_102__regCR0, 0, {  }, },
  { 2010 /* bnsctr- */, PPC::BCCCTR, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2018 /* bnsctrl */, PPC::BCCCTRL, Convert__imm_100__regCR0, 0, {  }, },
  { 2018 /* bnsctrl */, PPC::BCCCTRL, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2026 /* bnsctrl+ */, PPC::BCCCTRL, Convert__imm_103__regCR0, 0, {  }, },
  { 2026 /* bnsctrl+ */, PPC::BCCCTRL, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2035 /* bnsctrl- */, PPC::BCCCTRL, Convert__imm_102__regCR0, 0, {  }, },
  { 2035 /* bnsctrl- */, PPC::BCCCTRL, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2044 /* bnsl */, PPC::BCCL, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2044 /* bnsl */, PPC::BCCL, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2049 /* bnsl+ */, PPC::BCCL, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2049 /* bnsl+ */, PPC::BCCL, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2055 /* bnsl- */, PPC::BCCL, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2055 /* bnsl- */, PPC::BCCL, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2061 /* bnsla */, PPC::BCCLA, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2061 /* bnsla */, PPC::BCCLA, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2067 /* bnsla+ */, PPC::BCCLA, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2067 /* bnsla+ */, PPC::BCCLA, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2074 /* bnsla- */, PPC::BCCLA, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2074 /* bnsla- */, PPC::BCCLA, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2081 /* bnslr */, PPC::BCCLR, Convert__imm_100__regCR0, 0, {  }, },
  { 2081 /* bnslr */, PPC::BCCLR, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2087 /* bnslr+ */, PPC::BCCLR, Convert__imm_103__regCR0, 0, {  }, },
  { 2087 /* bnslr+ */, PPC::BCCLR, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2094 /* bnslr- */, PPC::BCCLR, Convert__imm_102__regCR0, 0, {  }, },
  { 2094 /* bnslr- */, PPC::BCCLR, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2101 /* bnslrl */, PPC::BCCLRL, Convert__imm_100__regCR0, 0, {  }, },
  { 2101 /* bnslrl */, PPC::BCCLRL, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2108 /* bnslrl+ */, PPC::BCCLRL, Convert__imm_103__regCR0, 0, {  }, },
  { 2108 /* bnslrl+ */, PPC::BCCLRL, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2116 /* bnslrl- */, PPC::BCCLRL, Convert__imm_102__regCR0, 0, {  }, },
  { 2116 /* bnslrl- */, PPC::BCCLRL, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2124 /* bnu */, PPC::BCC, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2124 /* bnu */, PPC::BCC, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2128 /* bnu+ */, PPC::BCC, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2128 /* bnu+ */, PPC::BCC, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2133 /* bnu- */, PPC::BCC, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2133 /* bnu- */, PPC::BCC, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2138 /* bnua */, PPC::BCCA, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2138 /* bnua */, PPC::BCCA, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2143 /* bnua+ */, PPC::BCCA, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2143 /* bnua+ */, PPC::BCCA, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2149 /* bnua- */, PPC::BCCA, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2149 /* bnua- */, PPC::BCCA, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2155 /* bnuctr */, PPC::BCCCTR, Convert__imm_100__regCR0, 0, {  }, },
  { 2155 /* bnuctr */, PPC::BCCCTR, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2162 /* bnuctr+ */, PPC::BCCCTR, Convert__imm_103__regCR0, 0, {  }, },
  { 2162 /* bnuctr+ */, PPC::BCCCTR, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2170 /* bnuctr- */, PPC::BCCCTR, Convert__imm_102__regCR0, 0, {  }, },
  { 2170 /* bnuctr- */, PPC::BCCCTR, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2178 /* bnuctrl */, PPC::BCCCTRL, Convert__imm_100__regCR0, 0, {  }, },
  { 2178 /* bnuctrl */, PPC::BCCCTRL, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2186 /* bnuctrl+ */, PPC::BCCCTRL, Convert__imm_103__regCR0, 0, {  }, },
  { 2186 /* bnuctrl+ */, PPC::BCCCTRL, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2195 /* bnuctrl- */, PPC::BCCCTRL, Convert__imm_102__regCR0, 0, {  }, },
  { 2195 /* bnuctrl- */, PPC::BCCCTRL, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2204 /* bnul */, PPC::BCCL, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2204 /* bnul */, PPC::BCCL, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2209 /* bnul+ */, PPC::BCCL, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2209 /* bnul+ */, PPC::BCCL, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2215 /* bnul- */, PPC::BCCL, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2215 /* bnul- */, PPC::BCCL, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2221 /* bnula */, PPC::BCCLA, Convert__imm_100__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2221 /* bnula */, PPC::BCCLA, Convert__imm_100__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2227 /* bnula+ */, PPC::BCCLA, Convert__imm_103__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2227 /* bnula+ */, PPC::BCCLA, Convert__imm_103__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2234 /* bnula- */, PPC::BCCLA, Convert__imm_102__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2234 /* bnula- */, PPC::BCCLA, Convert__imm_102__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2241 /* bnulr */, PPC::BCCLR, Convert__imm_100__regCR0, 0, {  }, },
  { 2241 /* bnulr */, PPC::BCCLR, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2247 /* bnulr+ */, PPC::BCCLR, Convert__imm_103__regCR0, 0, {  }, },
  { 2247 /* bnulr+ */, PPC::BCCLR, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2254 /* bnulr- */, PPC::BCCLR, Convert__imm_102__regCR0, 0, {  }, },
  { 2254 /* bnulr- */, PPC::BCCLR, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2261 /* bnulrl */, PPC::BCCLRL, Convert__imm_100__regCR0, 0, {  }, },
  { 2261 /* bnulrl */, PPC::BCCLRL, Convert__imm_100__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2268 /* bnulrl+ */, PPC::BCCLRL, Convert__imm_103__regCR0, 0, {  }, },
  { 2268 /* bnulrl+ */, PPC::BCCLRL, Convert__imm_103__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2276 /* bnulrl- */, PPC::BCCLRL, Convert__imm_102__regCR0, 0, {  }, },
  { 2276 /* bnulrl- */, PPC::BCCLRL, Convert__imm_102__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2284 /* brinc */, PPC::BRINC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2290 /* bso */, PPC::BCC, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2290 /* bso */, PPC::BCC, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2294 /* bso+ */, PPC::BCC, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2294 /* bso+ */, PPC::BCC, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2299 /* bso- */, PPC::BCC, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2299 /* bso- */, PPC::BCC, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2304 /* bsoa */, PPC::BCCA, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2304 /* bsoa */, PPC::BCCA, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2309 /* bsoa+ */, PPC::BCCA, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2309 /* bsoa+ */, PPC::BCCA, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2315 /* bsoa- */, PPC::BCCA, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2315 /* bsoa- */, PPC::BCCA, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2321 /* bsoctr */, PPC::BCCCTR, Convert__imm_108__regCR0, 0, {  }, },
  { 2321 /* bsoctr */, PPC::BCCCTR, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2328 /* bsoctr+ */, PPC::BCCCTR, Convert__imm_111__regCR0, 0, {  }, },
  { 2328 /* bsoctr+ */, PPC::BCCCTR, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2336 /* bsoctr- */, PPC::BCCCTR, Convert__imm_110__regCR0, 0, {  }, },
  { 2336 /* bsoctr- */, PPC::BCCCTR, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2344 /* bsoctrl */, PPC::BCCCTRL, Convert__imm_108__regCR0, 0, {  }, },
  { 2344 /* bsoctrl */, PPC::BCCCTRL, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2352 /* bsoctrl+ */, PPC::BCCCTRL, Convert__imm_111__regCR0, 0, {  }, },
  { 2352 /* bsoctrl+ */, PPC::BCCCTRL, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2361 /* bsoctrl- */, PPC::BCCCTRL, Convert__imm_110__regCR0, 0, {  }, },
  { 2361 /* bsoctrl- */, PPC::BCCCTRL, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2370 /* bsol */, PPC::BCCL, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2370 /* bsol */, PPC::BCCL, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2375 /* bsol+ */, PPC::BCCL, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2375 /* bsol+ */, PPC::BCCL, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2381 /* bsol- */, PPC::BCCL, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2381 /* bsol- */, PPC::BCCL, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2387 /* bsola */, PPC::BCCLA, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2387 /* bsola */, PPC::BCCLA, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2393 /* bsola+ */, PPC::BCCLA, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2393 /* bsola+ */, PPC::BCCLA, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2400 /* bsola- */, PPC::BCCLA, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2400 /* bsola- */, PPC::BCCLA, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2407 /* bsolr */, PPC::BCCLR, Convert__imm_108__regCR0, 0, {  }, },
  { 2407 /* bsolr */, PPC::BCCLR, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2413 /* bsolr+ */, PPC::BCCLR, Convert__imm_111__regCR0, 0, {  }, },
  { 2413 /* bsolr+ */, PPC::BCCLR, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2420 /* bsolr- */, PPC::BCCLR, Convert__imm_110__regCR0, 0, {  }, },
  { 2420 /* bsolr- */, PPC::BCCLR, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2427 /* bsolrl */, PPC::BCCLRL, Convert__imm_108__regCR0, 0, {  }, },
  { 2427 /* bsolrl */, PPC::BCCLRL, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2434 /* bsolrl+ */, PPC::BCCLRL, Convert__imm_111__regCR0, 0, {  }, },
  { 2434 /* bsolrl+ */, PPC::BCCLRL, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2442 /* bsolrl- */, PPC::BCCLRL, Convert__imm_110__regCR0, 0, {  }, },
  { 2442 /* bsolrl- */, PPC::BCCLRL, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2450 /* bt */, PPC::gBC, Convert__imm_12__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2453 /* bt+ */, PPC::gBC, Convert__imm_15__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2457 /* bt- */, PPC::gBC, Convert__imm_14__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2461 /* bta */, PPC::gBCA, Convert__imm_12__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2465 /* bta+ */, PPC::gBCA, Convert__imm_15__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2470 /* bta- */, PPC::gBCA, Convert__imm_14__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2475 /* btctr */, PPC::gBCCTR, Convert__imm_12__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2481 /* btctr+ */, PPC::gBCCTR, Convert__imm_15__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2488 /* btctr- */, PPC::gBCCTR, Convert__imm_14__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2495 /* btctrl */, PPC::gBCCTRL, Convert__imm_12__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2502 /* btctrl+ */, PPC::gBCCTRL, Convert__imm_15__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2510 /* btctrl- */, PPC::gBCCTRL, Convert__imm_14__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2518 /* btl */, PPC::gBCL, Convert__imm_12__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2522 /* btl+ */, PPC::gBCL, Convert__imm_15__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2527 /* btl- */, PPC::gBCL, Convert__imm_14__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2532 /* btla */, PPC::gBCLA, Convert__imm_12__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2537 /* btla+ */, PPC::gBCLA, Convert__imm_15__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2543 /* btla- */, PPC::gBCLA, Convert__imm_14__RegCRBITRC1_0__CondBr1_1, 0, { MCK_RegCRBITRC, MCK_CondBr }, },
  { 2549 /* btlr */, PPC::gBCLR, Convert__imm_12__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2554 /* btlr+ */, PPC::gBCLR, Convert__imm_15__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2560 /* btlr- */, PPC::gBCLR, Convert__imm_14__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2566 /* btlrl */, PPC::gBCLRL, Convert__imm_12__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2572 /* btlrl+ */, PPC::gBCLRL, Convert__imm_15__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2579 /* btlrl- */, PPC::gBCLRL, Convert__imm_14__RegCRBITRC1_0__imm_0, 0, { MCK_RegCRBITRC }, },
  { 2586 /* bun */, PPC::BCC, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2586 /* bun */, PPC::BCC, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2590 /* bun+ */, PPC::BCC, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2590 /* bun+ */, PPC::BCC, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2595 /* bun- */, PPC::BCC, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2595 /* bun- */, PPC::BCC, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2600 /* buna */, PPC::BCCA, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2600 /* buna */, PPC::BCCA, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2605 /* buna+ */, PPC::BCCA, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2605 /* buna+ */, PPC::BCCA, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2611 /* buna- */, PPC::BCCA, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2611 /* buna- */, PPC::BCCA, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2617 /* bunctr */, PPC::BCCCTR, Convert__imm_108__regCR0, 0, {  }, },
  { 2617 /* bunctr */, PPC::BCCCTR, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2624 /* bunctr+ */, PPC::BCCCTR, Convert__imm_111__regCR0, 0, {  }, },
  { 2624 /* bunctr+ */, PPC::BCCCTR, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2632 /* bunctr- */, PPC::BCCCTR, Convert__imm_110__regCR0, 0, {  }, },
  { 2632 /* bunctr- */, PPC::BCCCTR, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2640 /* bunctrl */, PPC::BCCCTRL, Convert__imm_108__regCR0, 0, {  }, },
  { 2640 /* bunctrl */, PPC::BCCCTRL, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2648 /* bunctrl+ */, PPC::BCCCTRL, Convert__imm_111__regCR0, 0, {  }, },
  { 2648 /* bunctrl+ */, PPC::BCCCTRL, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2657 /* bunctrl- */, PPC::BCCCTRL, Convert__imm_110__regCR0, 0, {  }, },
  { 2657 /* bunctrl- */, PPC::BCCCTRL, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2666 /* bunl */, PPC::BCCL, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2666 /* bunl */, PPC::BCCL, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2671 /* bunl+ */, PPC::BCCL, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2671 /* bunl+ */, PPC::BCCL, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2677 /* bunl- */, PPC::BCCL, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2677 /* bunl- */, PPC::BCCL, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2683 /* bunla */, PPC::BCCLA, Convert__imm_108__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2683 /* bunla */, PPC::BCCLA, Convert__imm_108__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2689 /* bunla+ */, PPC::BCCLA, Convert__imm_111__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2689 /* bunla+ */, PPC::BCCLA, Convert__imm_111__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2696 /* bunla- */, PPC::BCCLA, Convert__imm_110__regCR0__CondBr1_0, 0, { MCK_CondBr }, },
  { 2696 /* bunla- */, PPC::BCCLA, Convert__imm_110__RegCRRC1_0__CondBr1_1, 0, { MCK_RegCRRC, MCK_CondBr }, },
  { 2703 /* bunlr */, PPC::BCCLR, Convert__imm_108__regCR0, 0, {  }, },
  { 2703 /* bunlr */, PPC::BCCLR, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2709 /* bunlr+ */, PPC::BCCLR, Convert__imm_111__regCR0, 0, {  }, },
  { 2709 /* bunlr+ */, PPC::BCCLR, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2716 /* bunlr- */, PPC::BCCLR, Convert__imm_110__regCR0, 0, {  }, },
  { 2716 /* bunlr- */, PPC::BCCLR, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2723 /* bunlrl */, PPC::BCCLRL, Convert__imm_108__regCR0, 0, {  }, },
  { 2723 /* bunlrl */, PPC::BCCLRL, Convert__imm_108__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2730 /* bunlrl+ */, PPC::BCCLRL, Convert__imm_111__regCR0, 0, {  }, },
  { 2730 /* bunlrl+ */, PPC::BCCLRL, Convert__imm_111__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2738 /* bunlrl- */, PPC::BCCLRL, Convert__imm_110__regCR0, 0, {  }, },
  { 2738 /* bunlrl- */, PPC::BCCLRL, Convert__imm_110__RegCRRC1_0, 0, { MCK_RegCRRC }, },
  { 2746 /* clrldi */, PPC::RLDICL, Convert__RegG8RC1_0__RegG8RC1_1__imm_0__U6Imm1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 2746 /* clrldi */, PPC::RLDICLo, Convert__RegG8RC1_1__RegG8RC1_2__imm_0__U6Imm1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 2753 /* clrlsldi */, PPC::CLRLSLDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 2753 /* clrlsldi */, PPC::CLRLSLDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 2762 /* clrlslwi */, PPC::CLRLSLWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 2762 /* clrlslwi */, PPC::CLRLSLWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 2771 /* clrlwi */, PPC::RLWINM, Convert__RegGPRC1_0__RegGPRC1_1__imm_0__U5Imm1_2__imm_31, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 2771 /* clrlwi */, PPC::RLWINMo, Convert__RegGPRC1_1__RegGPRC1_2__imm_0__U5Imm1_3__imm_31, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 2778 /* clrrdi */, PPC::CLRRDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 2778 /* clrrdi */, PPC::CLRRDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 2785 /* clrrwi */, PPC::CLRRWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 2785 /* clrrwi */, PPC::CLRRWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 2792 /* cmp */, PPC::CMPW, Convert__RegCRRC1_0__RegGPRC1_2__RegGPRC1_3, 0, { MCK_RegCRRC, MCK_0, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2792 /* cmp */, PPC::CMPD, Convert__RegCRRC1_0__RegG8RC1_2__RegG8RC1_3, 0, { MCK_RegCRRC, MCK_1, MCK_RegG8RC, MCK_RegG8RC }, },
  { 2796 /* cmpb */, PPC::CMPB, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2801 /* cmpd */, PPC::CMPD, Convert__regCR0__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 2801 /* cmpd */, PPC::CMPD, Convert__RegCRRC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegCRRC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 2806 /* cmpdi */, PPC::CMPDI, Convert__regCR0__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 2806 /* cmpdi */, PPC::CMPDI, Convert__RegCRRC1_0__RegG8RC1_1__S16Imm1_2, 0, { MCK_RegCRRC, MCK_RegG8RC, MCK_S16Imm }, },
  { 2812 /* cmpi */, PPC::CMPWI, Convert__RegCRRC1_0__RegGPRC1_2__S16Imm1_3, 0, { MCK_RegCRRC, MCK_0, MCK_RegGPRC, MCK_S16Imm }, },
  { 2812 /* cmpi */, PPC::CMPDI, Convert__RegCRRC1_0__RegG8RC1_2__S16Imm1_3, 0, { MCK_RegCRRC, MCK_1, MCK_RegG8RC, MCK_S16Imm }, },
  { 2817 /* cmpl */, PPC::CMPLW, Convert__RegCRRC1_0__RegGPRC1_2__RegGPRC1_3, 0, { MCK_RegCRRC, MCK_0, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2817 /* cmpl */, PPC::CMPLD, Convert__RegCRRC1_0__RegG8RC1_2__RegG8RC1_3, 0, { MCK_RegCRRC, MCK_1, MCK_RegG8RC, MCK_RegG8RC }, },
  { 2822 /* cmpld */, PPC::CMPLD, Convert__regCR0__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 2822 /* cmpld */, PPC::CMPLD, Convert__RegCRRC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegCRRC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 2828 /* cmpldi */, PPC::CMPLDI, Convert__regCR0__RegG8RC1_0__U16Imm1_1, 0, { MCK_RegG8RC, MCK_U16Imm }, },
  { 2828 /* cmpldi */, PPC::CMPLDI, Convert__RegCRRC1_0__RegG8RC1_1__U16Imm1_2, 0, { MCK_RegCRRC, MCK_RegG8RC, MCK_U16Imm }, },
  { 2835 /* cmpli */, PPC::CMPLWI, Convert__RegCRRC1_0__RegGPRC1_2__U16Imm1_3, 0, { MCK_RegCRRC, MCK_0, MCK_RegGPRC, MCK_U16Imm }, },
  { 2835 /* cmpli */, PPC::CMPLDI, Convert__RegCRRC1_0__RegG8RC1_2__U16Imm1_3, 0, { MCK_RegCRRC, MCK_1, MCK_RegG8RC, MCK_U16Imm }, },
  { 2841 /* cmplw */, PPC::CMPLW, Convert__regCR0__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 2841 /* cmplw */, PPC::CMPLW, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2847 /* cmplwi */, PPC::CMPLWI, Convert__regCR0__RegGPRC1_0__U16Imm1_1, 0, { MCK_RegGPRC, MCK_U16Imm }, },
  { 2847 /* cmplwi */, PPC::CMPLWI, Convert__RegCRRC1_0__RegGPRC1_1__U16Imm1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 2854 /* cmpw */, PPC::CMPW, Convert__regCR0__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 2854 /* cmpw */, PPC::CMPW, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2859 /* cmpwi */, PPC::CMPWI, Convert__regCR0__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 2859 /* cmpwi */, PPC::CMPWI, Convert__RegCRRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 2865 /* cntlzd */, PPC::CNTLZD, Convert__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 2865 /* cntlzd */, PPC::CNTLZDo, Convert__RegG8RC1_1__RegG8RC1_2, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC }, },
  { 2872 /* cntlzw */, PPC::CNTLZW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 2872 /* cntlzw */, PPC::CNTLZWo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 2879 /* crand */, PPC::CRAND, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2885 /* crandc */, PPC::CRANDC, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2892 /* crclr */, PPC::CRXOR, Convert__RegCRBITRC1_0__RegCRBITRC1_0__RegCRBITRC1_0, 0, { MCK_RegCRBITRC }, },
  { 2898 /* creqv */, PPC::CREQV, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2904 /* crmove */, PPC::CROR, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_1, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2911 /* crnand */, PPC::CRNAND, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2918 /* crnor */, PPC::CRNOR, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2924 /* crnot */, PPC::CRNOR, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_1, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2930 /* cror */, PPC::CROR, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2935 /* crorc */, PPC::CRORC, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2941 /* crset */, PPC::CREQV, Convert__RegCRBITRC1_0__RegCRBITRC1_0__RegCRBITRC1_0, 0, { MCK_RegCRBITRC }, },
  { 2947 /* crxor */, PPC::CRXOR, Convert__RegCRBITRC1_0__RegCRBITRC1_1__RegCRBITRC1_2, 0, { MCK_RegCRBITRC, MCK_RegCRBITRC, MCK_RegCRBITRC }, },
  { 2953 /* dcba */, PPC::DCBA, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2958 /* dcbf */, PPC::DCBF, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2963 /* dcbi */, PPC::DCBI, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2968 /* dcbst */, PPC::DCBST, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2974 /* dcbt */, PPC::DCBT, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2979 /* dcbtst */, PPC::DCBTST, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2986 /* dcbz */, PPC::DCBZ, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2991 /* dcbzl */, PPC::DCBZL, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 2997 /* dccci */, PPC::DCCCI, Convert__regR0__regR0, 0, {  }, },
  { 2997 /* dccci */, PPC::DCCCI, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3003 /* dci */, PPC::DCCCI, Convert__regR0__regR0, 0, { MCK_0 }, },
  { 3007 /* divd */, PPC::DIVD, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 3007 /* divd */, PPC::DIVDo, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 3012 /* divdu */, PPC::DIVDU, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 3012 /* divdu */, PPC::DIVDUo, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 3018 /* divw */, PPC::DIVW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3018 /* divw */, PPC::DIVWo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3023 /* divwu */, PPC::DIVWU, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3023 /* divwu */, PPC::DIVWUo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3029 /* dss */, PPC::DSS, Convert__U5Imm1_0, 0, { MCK_U5Imm }, },
  { 3033 /* dssall */, PPC::DSSALL, Convert_NoOperands, 0, {  }, },
  { 3040 /* dst */, PPC::DST, Convert__U5Imm1_2__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 3044 /* dstst */, PPC::DSTST, Convert__U5Imm1_2__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 3050 /* dststt */, PPC::DSTSTT, Convert__U5Imm1_2__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 3057 /* dstt */, PPC::DSTT, Convert__U5Imm1_2__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 3062 /* eieio */, PPC::EnforceIEIO, Convert_NoOperands, 0, {  }, },
  { 3068 /* eqv */, PPC::EQV, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3068 /* eqv */, PPC::EQVo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3072 /* evabs */, PPC::EVABS, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3078 /* evaddiw */, PPC::EVADDIW, Convert__RegGPRC1_0__RegGPRC1_2__U5Imm1_1, 0, { MCK_RegGPRC, MCK_U5Imm, MCK_RegGPRC }, },
  { 3086 /* evaddsmiaaw */, PPC::EVADDSMIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3098 /* evaddssiaaw */, PPC::EVADDSSIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3110 /* evaddumiaaw */, PPC::EVADDUMIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3122 /* evaddusiaaw */, PPC::EVADDUSIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3134 /* evaddw */, PPC::EVADDW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3141 /* evand */, PPC::EVAND, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3147 /* evandc */, PPC::EVANDC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3154 /* evcmpeq */, PPC::EVCMPEQ, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3162 /* evcmpgts */, PPC::EVCMPGTS, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3171 /* evcmpgtu */, PPC::EVCMPGTU, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3180 /* evcmplts */, PPC::EVCMPLTS, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3189 /* evcmpltu */, PPC::EVCMPLTU, Convert__RegCRRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegCRRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3198 /* evcntlsw */, PPC::EVCNTLSW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3207 /* evcntlzw */, PPC::EVCNTLZW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3216 /* evdivws */, PPC::EVDIVWS, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3224 /* evdivwu */, PPC::EVDIVWU, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3232 /* eveqv */, PPC::EVEQV, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3238 /* evextsb */, PPC::EVEXTSB, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3246 /* evextsh */, PPC::EVEXTSH, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 3254 /* evldd */, PPC::EVLDD, Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE8, MCK_RegGxRCNoR0 }, },
  { 3260 /* evlddx */, PPC::EVLDDX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3267 /* evldh */, PPC::EVLDH, Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE8, MCK_RegGxRCNoR0 }, },
  { 3273 /* evldhx */, PPC::EVLDHX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3280 /* evldw */, PPC::EVLDW, Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE8, MCK_RegGxRCNoR0 }, },
  { 3286 /* evldwx */, PPC::EVLDWX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3293 /* evlhhesplat */, PPC::EVLHHESPLAT, Convert__RegGPRC1_0__DispSPE21_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE2, MCK_RegGxRCNoR0 }, },
  { 3305 /* evlhhesplatx */, PPC::EVLHHESPLATX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3318 /* evlhhossplat */, PPC::EVLHHOSSPLAT, Convert__RegGPRC1_0__DispSPE21_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE2, MCK_RegGxRCNoR0 }, },
  { 3331 /* evlhhossplatx */, PPC::EVLHHOSSPLATX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3345 /* evlhhousplat */, PPC::EVLHHOUSPLAT, Convert__RegGPRC1_0__DispSPE21_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE2, MCK_RegGxRCNoR0 }, },
  { 3358 /* evlhhousplatx */, PPC::EVLHHOUSPLATX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3372 /* evlwhe */, PPC::EVLWHE, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 3379 /* evlwhex */, PPC::EVLWHEX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3387 /* evlwhos */, PPC::EVLWHOS, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 3395 /* evlwhosx */, PPC::EVLWHOSX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3404 /* evlwhou */, PPC::EVLWHOU, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 3412 /* evlwhoux */, PPC::EVLWHOUX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3421 /* evlwhsplat */, PPC::EVLWHSPLAT, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 3432 /* evlwhsplatx */, PPC::EVLWHSPLATX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3444 /* evlwwsplat */, PPC::EVLWWSPLAT, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 3455 /* evlwwsplatx */, PPC::EVLWWSPLATX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3467 /* evmergehi */, PPC::EVMERGEHI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3477 /* evmergehilo */, PPC::EVMERGEHILO, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3489 /* evmergelo */, PPC::EVMERGELO, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3499 /* evmergelohi */, PPC::EVMERGELOHI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3511 /* evmhegsmfaa */, PPC::EVMHEGSMFAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3523 /* evmhegsmfan */, PPC::EVMHEGSMFAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3535 /* evmhegsmiaa */, PPC::EVMHEGSMIAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3547 /* evmhegsmian */, PPC::EVMHEGSMIAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3559 /* evmhegumiaa */, PPC::EVMHEGUMIAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3571 /* evmhegumian */, PPC::EVMHEGUMIAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3583 /* evmhesmf */, PPC::EVMHESMF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3592 /* evmhesmfa */, PPC::EVMHESMFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3602 /* evmhesmfaaw */, PPC::EVMHESMFAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3614 /* evmhesmfanw */, PPC::EVMHESMFANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3626 /* evmhesmi */, PPC::EVMHESMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3635 /* evmhesmia */, PPC::EVMHESMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3645 /* evmhesmiaaw */, PPC::EVMHESMIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3657 /* evmhesmianw */, PPC::EVMHESMIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3669 /* evmhessf */, PPC::EVMHESSF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3678 /* evmhessfa */, PPC::EVMHESSFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3688 /* evmhessfaaw */, PPC::EVMHESSFAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3700 /* evmhessfanw */, PPC::EVMHESSFANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3712 /* evmhessiaaw */, PPC::EVMHESSIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3724 /* evmhessianw */, PPC::EVMHESSIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3736 /* evmheumi */, PPC::EVMHEUMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3745 /* evmheumia */, PPC::EVMHEUMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3755 /* evmheumiaaw */, PPC::EVMHEUMIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3767 /* evmheumianw */, PPC::EVMHEUMIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3779 /* evmheusiaaw */, PPC::EVMHEUSIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3791 /* evmheusianw */, PPC::EVMHEUSIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3803 /* evmhogsmfaa */, PPC::EVMHOGSMFAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3815 /* evmhogsmfan */, PPC::EVMHOGSMFAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3827 /* evmhogsmiaa */, PPC::EVMHOGSMIAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3839 /* evmhogsmian */, PPC::EVMHOGSMIAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3851 /* evmhogumiaa */, PPC::EVMHOGUMIAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3863 /* evmhogumian */, PPC::EVMHOGUMIAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3875 /* evmhosmf */, PPC::EVMHOSMF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3884 /* evmhosmfa */, PPC::EVMHOSMFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3894 /* evmhosmfaaw */, PPC::EVMHOSMFAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3906 /* evmhosmfanw */, PPC::EVMHOSMFANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3918 /* evmhosmi */, PPC::EVMHOSMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3927 /* evmhosmia */, PPC::EVMHOSMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3937 /* evmhosmiaaw */, PPC::EVMHOSMIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3949 /* evmhosmianw */, PPC::EVMHOSMIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3961 /* evmhossf */, PPC::EVMHOSSF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3970 /* evmhossfa */, PPC::EVMHOSSFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3980 /* evmhossfaaw */, PPC::EVMHOSSFAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 3992 /* evmhossfanw */, PPC::EVMHOSSFANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4004 /* evmhossiaaw */, PPC::EVMHOSSIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4016 /* evmhossianw */, PPC::EVMHOSSIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4028 /* evmhoumi */, PPC::EVMHOUMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4037 /* evmhoumia */, PPC::EVMHOUMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4047 /* evmhoumiaaw */, PPC::EVMHOUMIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4059 /* evmhoumianw */, PPC::EVMHOUMIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4071 /* evmhousiaaw */, PPC::EVMHOUSIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4083 /* evmhousianw */, PPC::EVMHOUSIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4095 /* evmra */, PPC::EVMRA, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4101 /* evmwhsmf */, PPC::EVMWHSMF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4110 /* evmwhsmfa */, PPC::EVMWHSMFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4120 /* evmwhsmi */, PPC::EVMWHSMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4129 /* evmwhsmia */, PPC::EVMWHSMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4139 /* evmwhssf */, PPC::EVMWHSSF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4148 /* evmwhssfa */, PPC::EVMWHSSFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4158 /* evmwhumi */, PPC::EVMWHUMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4167 /* evmwhumia */, PPC::EVMWHUMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4177 /* evmwlsmiaaw */, PPC::EVMWLSMIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4189 /* evmwlsmianw */, PPC::EVMWLSMIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4201 /* evmwlssiaaw */, PPC::EVMWLSSIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4213 /* evmwlssianw */, PPC::EVMWLSSIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4225 /* evmwlumi */, PPC::EVMWLUMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4234 /* evmwlumia */, PPC::EVMWLUMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4244 /* evmwlumiaaw */, PPC::EVMWLUMIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4256 /* evmwlumianw */, PPC::EVMWLUMIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4268 /* evmwlusiaaw */, PPC::EVMWLUSIAAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4280 /* evmwlusianw */, PPC::EVMWLUSIANW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4292 /* evmwsmf */, PPC::EVMWSMF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4300 /* evmwsmfa */, PPC::EVMWSMFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4309 /* evmwsmfaa */, PPC::EVMWSMFAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4319 /* evmwsmfan */, PPC::EVMWSMFAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4329 /* evmwsmi */, PPC::EVMWSMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4337 /* evmwsmia */, PPC::EVMWSMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4346 /* evmwsmiaa */, PPC::EVMWSMIAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4356 /* evmwsmian */, PPC::EVMWSMIAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4366 /* evmwssf */, PPC::EVMWSSF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4374 /* evmwssfa */, PPC::EVMWSSFA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4383 /* evmwssfaa */, PPC::EVMWSSFAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4393 /* evmwssfan */, PPC::EVMWSSFAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4403 /* evmwumi */, PPC::EVMWUMI, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4411 /* evmwumia */, PPC::EVMWUMIA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4420 /* evmwumiaa */, PPC::EVMWUMIAA, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4430 /* evmwumian */, PPC::EVMWUMIAN, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4440 /* evnand */, PPC::EVNAND, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4447 /* evneg */, PPC::EVNEG, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4453 /* evnor */, PPC::EVNOR, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4459 /* evor */, PPC::EVOR, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4464 /* evorc */, PPC::EVORC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4470 /* evrlw */, PPC::EVRLW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4476 /* evrlwi */, PPC::EVRLWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 4483 /* evrndw */, PPC::EVRNDW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4490 /* evslw */, PPC::EVSLW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4496 /* evslwi */, PPC::EVSLWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 4503 /* evsplatfi */, PPC::EVSPLATFI, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 4513 /* evsplati */, PPC::EVSPLATI, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 4522 /* evsrwis */, PPC::EVSRWIS, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 4530 /* evsrwiu */, PPC::EVSRWIU, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 4538 /* evsrws */, PPC::EVSRWS, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4545 /* evsrwu */, PPC::EVSRWU, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4552 /* evstdd */, PPC::EVSTDD, Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE8, MCK_RegGxRCNoR0 }, },
  { 4559 /* evstddx */, PPC::EVSTDDX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4567 /* evstdh */, PPC::EVSTDH, Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE8, MCK_RegGxRCNoR0 }, },
  { 4574 /* evstdhx */, PPC::EVSTDHX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4582 /* evstdw */, PPC::EVSTDW, Convert__RegGPRC1_0__DispSPE81_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE8, MCK_RegGxRCNoR0 }, },
  { 4589 /* evstdwx */, PPC::EVSTDWX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4597 /* evstwhe */, PPC::EVSTWHE, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 4605 /* evstwhex */, PPC::EVSTWHEX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4614 /* evstwho */, PPC::EVSTWHO, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 4622 /* evstwhox */, PPC::EVSTWHOX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4631 /* evstwwe */, PPC::EVSTWWE, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 4639 /* evstwwex */, PPC::EVSTWWEX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4648 /* evstwwo */, PPC::EVSTWWO, Convert__RegGPRC1_0__DispSPE41_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispSPE4, MCK_RegGxRCNoR0 }, },
  { 4656 /* evstwwox */, PPC::EVSTWWOX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4665 /* evsubfsmiaaw */, PPC::EVSUBFSMIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4678 /* evsubfssiaaw */, PPC::EVSUBFSSIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4691 /* evsubfumiaaw */, PPC::EVSUBFUMIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4704 /* evsubfusiaaw */, PPC::EVSUBFUSIAAW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4717 /* evsubfw */, PPC::EVSUBFW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4725 /* evsubifw */, PPC::EVSUBIFW, Convert__RegGPRC1_0__U5Imm1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_U5Imm, MCK_RegGPRC }, },
  { 4734 /* evxor */, PPC::EVXOR, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4740 /* extldi */, PPC::EXTLDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 4740 /* extldi */, PPC::EXTLDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 4747 /* extlwi */, PPC::EXTLWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 4747 /* extlwi */, PPC::EXTLWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 4754 /* extrdi */, PPC::EXTRDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 4754 /* extrdi */, PPC::EXTRDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 4761 /* extrwi */, PPC::EXTRWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 4761 /* extrwi */, PPC::EXTRWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 4768 /* extsb */, PPC::EXTSB, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4768 /* extsb */, PPC::EXTSBo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4774 /* extsh */, PPC::EXTSH, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 4774 /* extsh */, PPC::EXTSHo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 4780 /* extsw */, PPC::EXTSW, Convert__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 4780 /* extsw */, PPC::EXTSWo, Convert__RegG8RC1_1__RegG8RC1_2, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC }, },
  { 4786 /* fabs */, PPC::FABSS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4786 /* fabs */, PPC::FABSSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4791 /* fadd */, PPC::FADD, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4791 /* fadd */, PPC::FADDo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4796 /* fadds */, PPC::FADDS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4796 /* fadds */, PPC::FADDSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4802 /* fcfid */, PPC::FCFID, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4802 /* fcfid */, PPC::FCFIDo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4808 /* fcfids */, PPC::FCFIDS, Convert__RegF4RC1_0__RegF8RC1_1, 0, { MCK_RegF4RC, MCK_RegF8RC }, },
  { 4808 /* fcfids */, PPC::FCFIDSo, Convert__RegF4RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF8RC }, },
  { 4815 /* fcfidu */, PPC::FCFIDU, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4815 /* fcfidu */, PPC::FCFIDUo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4822 /* fcfidus */, PPC::FCFIDUS, Convert__RegF4RC1_0__RegF8RC1_1, 0, { MCK_RegF4RC, MCK_RegF8RC }, },
  { 4822 /* fcfidus */, PPC::FCFIDUSo, Convert__RegF4RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF8RC }, },
  { 4830 /* fcmpu */, PPC::FCMPUS, Convert__RegCRRC1_0__RegF4RC1_1__RegF4RC1_2, 0, { MCK_RegCRRC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4836 /* fcpsgn */, PPC::FCPSGNS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4836 /* fcpsgn */, PPC::FCPSGNSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4843 /* fctid */, PPC::FCTID, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4843 /* fctid */, PPC::FCTIDo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4849 /* fctiduz */, PPC::FCTIDUZ, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4849 /* fctiduz */, PPC::FCTIDUZo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4857 /* fctidz */, PPC::FCTIDZ, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4857 /* fctidz */, PPC::FCTIDZo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4864 /* fctiw */, PPC::FCTIW, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4864 /* fctiw */, PPC::FCTIWo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4870 /* fctiwuz */, PPC::FCTIWUZ, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4870 /* fctiwuz */, PPC::FCTIWUZo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4878 /* fctiwz */, PPC::FCTIWZ, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4878 /* fctiwz */, PPC::FCTIWZo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4885 /* fdiv */, PPC::FDIV, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4885 /* fdiv */, PPC::FDIVo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4890 /* fdivs */, PPC::FDIVS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4890 /* fdivs */, PPC::FDIVSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4896 /* fmadd */, PPC::FMADD, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4896 /* fmadd */, PPC::FMADDo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3__RegF8RC1_4, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4902 /* fmadds */, PPC::FMADDS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4902 /* fmadds */, PPC::FMADDSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3__RegF4RC1_4, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4909 /* fmr */, PPC::FMR, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4909 /* fmr */, PPC::FMRo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4913 /* fmsub */, PPC::FMSUB, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4913 /* fmsub */, PPC::FMSUBo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3__RegF8RC1_4, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4919 /* fmsubs */, PPC::FMSUBS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4919 /* fmsubs */, PPC::FMSUBSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3__RegF4RC1_4, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4926 /* fmul */, PPC::FMUL, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4926 /* fmul */, PPC::FMULo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4931 /* fmuls */, PPC::FMULS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4931 /* fmuls */, PPC::FMULSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4937 /* fnabs */, PPC::FNABSS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4937 /* fnabs */, PPC::FNABSSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4943 /* fneg */, PPC::FNEGS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4943 /* fneg */, PPC::FNEGSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4948 /* fnmadd */, PPC::FNMADD, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4948 /* fnmadd */, PPC::FNMADDo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3__RegF8RC1_4, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4955 /* fnmadds */, PPC::FNMADDS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4955 /* fnmadds */, PPC::FNMADDSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3__RegF4RC1_4, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4963 /* fnmsub */, PPC::FNMSUB, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4963 /* fnmsub */, PPC::FNMSUBo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3__RegF8RC1_4, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4970 /* fnmsubs */, PPC::FNMSUBS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4970 /* fnmsubs */, PPC::FNMSUBSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3__RegF4RC1_4, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4978 /* fre */, PPC::FRE, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 4978 /* fre */, PPC::FREo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 4982 /* fres */, PPC::FRES, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4982 /* fres */, PPC::FRESo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4987 /* frim */, PPC::FRIMS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4987 /* frim */, PPC::FRIMSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4992 /* frin */, PPC::FRINS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4992 /* frin */, PPC::FRINSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 4997 /* frip */, PPC::FRIPS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 4997 /* frip */, PPC::FRIPSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5002 /* friz */, PPC::FRIZS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 5002 /* friz */, PPC::FRIZSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5007 /* frsp */, PPC::FRSP, Convert__RegF4RC1_0__RegF8RC1_1, 0, { MCK_RegF4RC, MCK_RegF8RC }, },
  { 5007 /* frsp */, PPC::FRSPo, Convert__RegF4RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF8RC }, },
  { 5012 /* frsqrte */, PPC::FRSQRTE, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 5012 /* frsqrte */, PPC::FRSQRTEo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 5020 /* frsqrtes */, PPC::FRSQRTES, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 5020 /* frsqrtes */, PPC::FRSQRTESo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5029 /* fsel */, PPC::FSELS, Convert__RegF4RC1_0__RegF8RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK_RegF4RC, MCK_RegF8RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5029 /* fsel */, PPC::FSELSo, Convert__RegF4RC1_1__RegF8RC1_2__RegF4RC1_3__RegF4RC1_4, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF8RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5034 /* fsqrt */, PPC::FSQRT, Convert__RegF8RC1_0__RegF8RC1_1, 0, { MCK_RegF8RC, MCK_RegF8RC }, },
  { 5034 /* fsqrt */, PPC::FSQRTo, Convert__RegF8RC1_1__RegF8RC1_2, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC }, },
  { 5040 /* fsqrts */, PPC::FSQRTS, Convert__RegF4RC1_0__RegF4RC1_1, 0, { MCK_RegF4RC, MCK_RegF4RC }, },
  { 5040 /* fsqrts */, PPC::FSQRTSo, Convert__RegF4RC1_1__RegF4RC1_2, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5047 /* fsub */, PPC::FSUB, Convert__RegF8RC1_0__RegF8RC1_1__RegF8RC1_2, 0, { MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 5047 /* fsub */, PPC::FSUBo, Convert__RegF8RC1_1__RegF8RC1_2__RegF8RC1_3, 0, { MCK__DOT_, MCK_RegF8RC, MCK_RegF8RC, MCK_RegF8RC }, },
  { 5052 /* fsubs */, PPC::FSUBS, Convert__RegF4RC1_0__RegF4RC1_1__RegF4RC1_2, 0, { MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5052 /* fsubs */, PPC::FSUBSo, Convert__RegF4RC1_1__RegF4RC1_2__RegF4RC1_3, 0, { MCK__DOT_, MCK_RegF4RC, MCK_RegF4RC, MCK_RegF4RC }, },
  { 5058 /* icbi */, PPC::ICBI, Convert__RegGxRCNoR01_0__RegGxRC1_1, 0, { MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5063 /* icbt */, PPC::ICBT, Convert__U4Imm1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_U4Imm, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5068 /* iccci */, PPC::ICCCI, Convert__regR0__regR0, 0, {  }, },
  { 5068 /* iccci */, PPC::ICCCI, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 5074 /* ici */, PPC::ICCCI, Convert__regR0__regR0, 0, { MCK_0 }, },
  { 5078 /* inslwi */, PPC::INSLWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 5078 /* inslwi */, PPC::INSLWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 5085 /* insrdi */, PPC::INSRDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 5085 /* insrdi */, PPC::INSRDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 5092 /* insrwi */, PPC::INSRWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 5092 /* insrwi */, PPC::INSRWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 5099 /* isel */, PPC::ISEL, Convert__RegGPRC1_0__RegGPRCNoR01_1__RegGPRC1_2__RegCRBITRC1_3, 0, { MCK_RegGPRC, MCK_RegGPRCNoR0, MCK_RegGPRC, MCK_RegCRBITRC }, },
  { 5104 /* isync */, PPC::ISYNC, Convert_NoOperands, 0, {  }, },
  { 5110 /* la */, PPC::LAx, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5113 /* lbz */, PPC::LBZ, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5117 /* lbzcix */, PPC::LBZCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 5124 /* lbzu */, PPC::LBZU, Convert__RegGPRC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5129 /* lbzux */, PPC::LBZUX, Convert__RegGPRC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5135 /* lbzx */, PPC::LBZX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5140 /* ld */, PPC::LD, Convert__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2, 0, { MCK_RegG8RC, MCK_DispRIX, MCK_RegGxRCNoR0 }, },
  { 5143 /* ldarx */, PPC::LDARX, Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5149 /* ldbrx */, PPC::LDBRX, Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5155 /* ldcix */, PPC::LDCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 5161 /* ldu */, PPC::LDU, Convert__RegG8RC1_0__imm_0__DispRIX1_1__RegGxRCNoR01_2, 0, { MCK_RegG8RC, MCK_DispRIX, MCK_RegGxRCNoR0 }, },
  { 5165 /* ldux */, PPC::LDUX, Convert__RegG8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5170 /* ldx */, PPC::LDX, Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5174 /* lfd */, PPC::LFD, Convert__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF8RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5178 /* lfdu */, PPC::LFDU, Convert__RegF8RC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF8RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5183 /* lfdux */, PPC::LFDUX, Convert__RegF8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5189 /* lfdx */, PPC::LFDX, Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5194 /* lfiwax */, PPC::LFIWAX, Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5201 /* lfiwzx */, PPC::LFIWZX, Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5208 /* lfs */, PPC::LFS, Convert__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF4RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5212 /* lfsu */, PPC::LFSU, Convert__RegF4RC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF4RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5217 /* lfsux */, PPC::LFSUX, Convert__RegF4RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF4RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5223 /* lfsx */, PPC::LFSX, Convert__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF4RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5228 /* lha */, PPC::LHA, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5232 /* lhau */, PPC::LHAU, Convert__RegGPRC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5237 /* lhaux */, PPC::LHAUX, Convert__RegGPRC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5243 /* lhax */, PPC::LHAX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5248 /* lhbrx */, PPC::LHBRX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5254 /* lhz */, PPC::LHZ, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5258 /* lhzcix */, PPC::LHZCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 5265 /* lhzu */, PPC::LHZU, Convert__RegGPRC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5270 /* lhzux */, PPC::LHZUX, Convert__RegGPRC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5276 /* lhzx */, PPC::LHZX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5281 /* li */, PPC::LI, Convert__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 5284 /* lis */, PPC::LIS, Convert__RegGPRC1_0__S17Imm1_1, 0, { MCK_RegGPRC, MCK_S17Imm }, },
  { 5288 /* lmw */, PPC::LMW, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5292 /* lswi */, PPC::LSWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 5297 /* lvebx */, PPC::LVEBX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5303 /* lvehx */, PPC::LVEHX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5309 /* lvewx */, PPC::LVEWX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5315 /* lvsl */, PPC::LVSL, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5320 /* lvsr */, PPC::LVSR, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5325 /* lvx */, PPC::LVX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5329 /* lvxl */, PPC::LVXL, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5334 /* lwa */, PPC::LWA, Convert__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2, 0, { MCK_RegG8RC, MCK_DispRIX, MCK_RegGxRCNoR0 }, },
  { 5338 /* lwarx */, PPC::LWARX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5344 /* lwaux */, PPC::LWAUX, Convert__RegG8RC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5350 /* lwax */, PPC::LWAX, Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5355 /* lwbrx */, PPC::LWBRX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5361 /* lwsync */, PPC::SYNC, Convert__imm_1, 0, {  }, },
  { 5368 /* lwz */, PPC::LWZ, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5372 /* lwzcix */, PPC::LWZCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 5379 /* lwzu */, PPC::LWZU, Convert__RegGPRC1_0__imm_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 5384 /* lwzux */, PPC::LWZUX, Convert__RegGPRC1_0__imm_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5390 /* lwzx */, PPC::LWZX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5395 /* lxsdx */, PPC::LXSDX, Convert__RegVSFRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSFRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5401 /* lxvd2x */, PPC::LXVD2X, Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5408 /* lxvdsx */, PPC::LXVDSX, Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5415 /* lxvw4x */, PPC::LXVW4X, Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 5422 /* mbar */, PPC::MBAR, Convert__imm_0, 0, {  }, },
  { 5422 /* mbar */, PPC::MBAR, Convert__U5Imm1_0, 0, { MCK_U5Imm }, },
  { 5427 /* mcrf */, PPC::MCRF, Convert__RegCRRC1_0__RegCRRC1_1, 0, { MCK_RegCRRC, MCK_RegCRRC }, },
  { 5432 /* mfamr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_29, 0, { MCK_RegGPRC }, },
  { 5438 /* mfasr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_280, 0, { MCK_RegGPRC }, },
  { 5444 /* mfbr0 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_128, 0, { MCK_RegGPRC }, },
  { 5450 /* mfbr1 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_129, 0, { MCK_RegGPRC }, },
  { 5456 /* mfbr2 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_130, 0, { MCK_RegGPRC }, },
  { 5462 /* mfbr3 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_131, 0, { MCK_RegGPRC }, },
  { 5468 /* mfbr4 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_132, 0, { MCK_RegGPRC }, },
  { 5474 /* mfbr5 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_133, 0, { MCK_RegGPRC }, },
  { 5480 /* mfbr6 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_134, 0, { MCK_RegGPRC }, },
  { 5486 /* mfbr7 */, PPC::MFDCR, Convert__RegGPRC1_0__imm_135, 0, { MCK_RegGPRC }, },
  { 5492 /* mfcfar */, PPC::MFSPR, Convert__RegGPRC1_0__imm_28, 0, { MCK_RegGPRC }, },
  { 5499 /* mfcr */, PPC::MFCR, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5504 /* mfctr */, PPC::MFCTR, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5510 /* mfdar */, PPC::MFSPR, Convert__RegGPRC1_0__imm_19, 0, { MCK_RegGPRC }, },
  { 5516 /* mfdbatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_537, 0, { MCK_RegGPRC, MCK_0 }, },
  { 5516 /* mfdbatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_539, 0, { MCK_RegGPRC, MCK_1 }, },
  { 5516 /* mfdbatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_541, 0, { MCK_RegGPRC, MCK_2 }, },
  { 5516 /* mfdbatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_543, 0, { MCK_RegGPRC, MCK_3 }, },
  { 5524 /* mfdbatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_536, 0, { MCK_RegGPRC, MCK_0 }, },
  { 5524 /* mfdbatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_538, 0, { MCK_RegGPRC, MCK_1 }, },
  { 5524 /* mfdbatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_540, 0, { MCK_RegGPRC, MCK_2 }, },
  { 5524 /* mfdbatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_542, 0, { MCK_RegGPRC, MCK_3 }, },
  { 5532 /* mfdccr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_1018, 0, { MCK_RegGPRC }, },
  { 5539 /* mfdcr */, PPC::MFDCR, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 5545 /* mfdear */, PPC::MFSPR, Convert__RegGPRC1_0__imm_981, 0, { MCK_RegGPRC }, },
  { 5552 /* mfdec */, PPC::MFSPR, Convert__RegGPRC1_0__imm_22, 0, { MCK_RegGPRC }, },
  { 5552 /* mfdec */, PPC::MFSPR, Convert__RegGPRC1_0__imm_22, 0, { MCK_RegGPRC }, },
  { 5558 /* mfdscr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_17, 0, { MCK_RegGPRC }, },
  { 5565 /* mfdsisr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_18, 0, { MCK_RegGPRC }, },
  { 5573 /* mfesr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_980, 0, { MCK_RegGPRC }, },
  { 5579 /* mffs */, PPC::MFFS, Convert__RegF8RC1_0, 0, { MCK_RegF8RC }, },
  { 5584 /* mfibatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_529, 0, { MCK_RegGPRC, MCK_0 }, },
  { 5584 /* mfibatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_531, 0, { MCK_RegGPRC, MCK_1 }, },
  { 5584 /* mfibatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_533, 0, { MCK_RegGPRC, MCK_2 }, },
  { 5584 /* mfibatl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_535, 0, { MCK_RegGPRC, MCK_3 }, },
  { 5592 /* mfibatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_528, 0, { MCK_RegGPRC, MCK_0 }, },
  { 5592 /* mfibatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_530, 0, { MCK_RegGPRC, MCK_1 }, },
  { 5592 /* mfibatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_532, 0, { MCK_RegGPRC, MCK_2 }, },
  { 5592 /* mfibatu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_534, 0, { MCK_RegGPRC, MCK_3 }, },
  { 5600 /* mficcr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_1019, 0, { MCK_RegGPRC }, },
  { 5607 /* mflr */, PPC::MFLR, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5612 /* mfmsr */, PPC::MFMSR, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5618 /* mfocrf */, PPC::MFOCRF, Convert__RegGPRC1_0__CRBitMask1_1, 0, { MCK_RegGPRC, MCK_CRBitMask }, },
  { 5625 /* mfpid */, PPC::MFSPR, Convert__RegGPRC1_0__imm_48, 0, { MCK_RegGPRC }, },
  { 5631 /* mfpvr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_287, 0, { MCK_RegGPRC }, },
  { 5637 /* mfrtcl */, PPC::MFSPR, Convert__RegGPRC1_0__imm_5, 0, { MCK_RegGPRC }, },
  { 5644 /* mfrtcu */, PPC::MFSPR, Convert__RegGPRC1_0__imm_4, 0, { MCK_RegGPRC }, },
  { 5651 /* mfsdr1 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_25, 0, { MCK_RegGPRC }, },
  { 5651 /* mfsdr1 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_25, 0, { MCK_RegGPRC }, },
  { 5658 /* mfspefscr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_512, 0, { MCK_RegGPRC }, },
  { 5668 /* mfspr */, PPC::MFSPR, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_272, 0, { MCK_RegGPRC, MCK_0 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_273, 0, { MCK_RegGPRC, MCK_1 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_274, 0, { MCK_RegGPRC, MCK_2 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_275, 0, { MCK_RegGPRC, MCK_3 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_260, 0, { MCK_RegGPRC, MCK_4 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_261, 0, { MCK_RegGPRC, MCK_5 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_262, 0, { MCK_RegGPRC, MCK_6 }, },
  { 5674 /* mfsprg */, PPC::MFSPR, Convert__RegGPRC1_0__imm_263, 0, { MCK_RegGPRC, MCK_7 }, },
  { 5681 /* mfsprg0 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_272, 0, { MCK_RegGPRC }, },
  { 5689 /* mfsprg1 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_273, 0, { MCK_RegGPRC }, },
  { 5697 /* mfsprg2 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_274, 0, { MCK_RegGPRC }, },
  { 5705 /* mfsprg3 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_275, 0, { MCK_RegGPRC }, },
  { 5713 /* mfsprg4 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_260, 0, { MCK_RegGPRC }, },
  { 5721 /* mfsprg5 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_261, 0, { MCK_RegGPRC }, },
  { 5729 /* mfsprg6 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_262, 0, { MCK_RegGPRC }, },
  { 5737 /* mfsprg7 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_263, 0, { MCK_RegGPRC }, },
  { 5745 /* mfsr */, PPC::MFSR, Convert__RegGPRC1_0__U4Imm1_1, 0, { MCK_RegGPRC, MCK_U4Imm }, },
  { 5750 /* mfsrin */, PPC::MFSRIN, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 5757 /* mfsrr0 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_26, 0, { MCK_RegGPRC }, },
  { 5757 /* mfsrr0 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_26, 0, { MCK_RegGPRC }, },
  { 5764 /* mfsrr1 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_27, 0, { MCK_RegGPRC }, },
  { 5764 /* mfsrr1 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_27, 0, { MCK_RegGPRC }, },
  { 5771 /* mfsrr2 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_990, 0, { MCK_RegGPRC }, },
  { 5778 /* mfsrr3 */, PPC::MFSPR, Convert__RegGPRC1_0__imm_991, 0, { MCK_RegGPRC }, },
  { 5785 /* mftb */, PPC::MFTB, Convert__RegGPRC1_0__imm_268, 0, { MCK_RegGPRC }, },
  { 5785 /* mftb */, PPC::MFTB, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 5790 /* mftbhi */, PPC::MFSPR, Convert__RegGPRC1_0__imm_988, 0, { MCK_RegGPRC }, },
  { 5797 /* mftbl */, PPC::MFTB, Convert__RegGPRC1_0__imm_268, 0, { MCK_RegGPRC }, },
  { 5803 /* mftblo */, PPC::MFSPR, Convert__RegGPRC1_0__imm_989, 0, { MCK_RegGPRC }, },
  { 5810 /* mftbu */, PPC::MFTB, Convert__RegGPRC1_0__imm_269, 0, { MCK_RegGPRC }, },
  { 5816 /* mftcr */, PPC::MFSPR, Convert__RegGPRC1_0__imm_986, 0, { MCK_RegGPRC }, },
  { 5822 /* mfvscr */, PPC::MFVSCR, Convert__RegVRRC1_0, 0, { MCK_RegVRRC }, },
  { 5829 /* mfxer */, PPC::MFSPR, Convert__RegGPRC1_0__imm_1, 0, { MCK_RegGPRC }, },
  { 5835 /* mr */, PPC::OR8, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 5835 /* mr */, PPC::OR8o, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_2, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC }, },
  { 5838 /* msync */, PPC::SYNC, Convert__imm_0, 0, {  }, },
  { 5844 /* mtamr */, PPC::MTSPR, Convert__imm_29__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5850 /* mtasr */, PPC::MTSPR, Convert__imm_280__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5850 /* mtasr */, PPC::MTSPR, Convert__imm_280__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5856 /* mtbr0 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_128, 0, { MCK_RegGPRC }, },
  { 5862 /* mtbr1 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_129, 0, { MCK_RegGPRC }, },
  { 5868 /* mtbr2 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_130, 0, { MCK_RegGPRC }, },
  { 5874 /* mtbr3 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_131, 0, { MCK_RegGPRC }, },
  { 5880 /* mtbr4 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_132, 0, { MCK_RegGPRC }, },
  { 5886 /* mtbr5 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_133, 0, { MCK_RegGPRC }, },
  { 5892 /* mtbr6 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_134, 0, { MCK_RegGPRC }, },
  { 5898 /* mtbr7 */, PPC::MTDCR, Convert__RegGPRC1_0__imm_135, 0, { MCK_RegGPRC }, },
  { 5904 /* mtcfar */, PPC::MTSPR, Convert__imm_28__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5911 /* mtcr */, PPC::MTCRF8, Convert__imm_255__RegG8RC1_0, 0, { MCK_RegG8RC }, },
  { 5916 /* mtcrf */, PPC::MTCRF, Convert__Imm1_0__RegGPRC1_1, 0, { MCK_Imm, MCK_RegGPRC }, },
  { 5922 /* mtctr */, PPC::MTCTR, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5928 /* mtdar */, PPC::MTSPR, Convert__imm_19__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5934 /* mtdbatl */, PPC::MTSPR, Convert__imm_537__RegGPRC1_1, 0, { MCK_0, MCK_RegGPRC }, },
  { 5934 /* mtdbatl */, PPC::MTSPR, Convert__imm_539__RegGPRC1_1, 0, { MCK_1, MCK_RegGPRC }, },
  { 5934 /* mtdbatl */, PPC::MTSPR, Convert__imm_541__RegGPRC1_1, 0, { MCK_2, MCK_RegGPRC }, },
  { 5934 /* mtdbatl */, PPC::MTSPR, Convert__imm_543__RegGPRC1_1, 0, { MCK_3, MCK_RegGPRC }, },
  { 5942 /* mtdbatu */, PPC::MTSPR, Convert__imm_536__RegGPRC1_1, 0, { MCK_0, MCK_RegGPRC }, },
  { 5942 /* mtdbatu */, PPC::MTSPR, Convert__imm_538__RegGPRC1_1, 0, { MCK_1, MCK_RegGPRC }, },
  { 5942 /* mtdbatu */, PPC::MTSPR, Convert__imm_540__RegGPRC1_1, 0, { MCK_2, MCK_RegGPRC }, },
  { 5942 /* mtdbatu */, PPC::MTSPR, Convert__imm_542__RegGPRC1_1, 0, { MCK_3, MCK_RegGPRC }, },
  { 5950 /* mtdccr */, PPC::MTSPR, Convert__imm_1018__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5957 /* mtdcr */, PPC::MTDCR, Convert__RegGPRC1_1__Imm1_0, 0, { MCK_Imm, MCK_RegGPRC }, },
  { 5963 /* mtdear */, PPC::MTSPR, Convert__imm_981__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5970 /* mtdec */, PPC::MTSPR, Convert__imm_22__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5970 /* mtdec */, PPC::MTSPR, Convert__imm_22__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5976 /* mtdscr */, PPC::MTSPR, Convert__imm_17__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5983 /* mtdsisr */, PPC::MTSPR, Convert__imm_18__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5991 /* mtesr */, PPC::MTSPR, Convert__imm_980__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 5997 /* mtfsb0 */, PPC::MTFSB0, Convert__U5Imm1_0, 0, { MCK_U5Imm }, },
  { 6004 /* mtfsb1 */, PPC::MTFSB1, Convert__U5Imm1_0, 0, { MCK_U5Imm }, },
  { 6011 /* mtfsf */, PPC::MTFSF, Convert__Imm1_0__RegF8RC1_1, 0, { MCK_Imm, MCK_RegF8RC }, },
  { 6017 /* mtibatl */, PPC::MTSPR, Convert__imm_529__RegGPRC1_1, 0, { MCK_0, MCK_RegGPRC }, },
  { 6017 /* mtibatl */, PPC::MTSPR, Convert__imm_531__RegGPRC1_1, 0, { MCK_1, MCK_RegGPRC }, },
  { 6017 /* mtibatl */, PPC::MTSPR, Convert__imm_533__RegGPRC1_1, 0, { MCK_2, MCK_RegGPRC }, },
  { 6017 /* mtibatl */, PPC::MTSPR, Convert__imm_535__RegGPRC1_1, 0, { MCK_3, MCK_RegGPRC }, },
  { 6025 /* mtibatu */, PPC::MTSPR, Convert__imm_528__RegGPRC1_1, 0, { MCK_0, MCK_RegGPRC }, },
  { 6025 /* mtibatu */, PPC::MTSPR, Convert__imm_530__RegGPRC1_1, 0, { MCK_1, MCK_RegGPRC }, },
  { 6025 /* mtibatu */, PPC::MTSPR, Convert__imm_532__RegGPRC1_1, 0, { MCK_2, MCK_RegGPRC }, },
  { 6025 /* mtibatu */, PPC::MTSPR, Convert__imm_534__RegGPRC1_1, 0, { MCK_3, MCK_RegGPRC }, },
  { 6033 /* mticcr */, PPC::MTSPR, Convert__imm_1019__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6040 /* mtlr */, PPC::MTLR, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6045 /* mtmsr */, PPC::MTMSR, Convert__RegGPRC1_0__imm_0, 0, { MCK_RegGPRC }, },
  { 6045 /* mtmsr */, PPC::MTMSR, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 6051 /* mtmsrd */, PPC::MTMSRD, Convert__RegGPRC1_0__imm_0, 0, { MCK_RegGPRC }, },
  { 6051 /* mtmsrd */, PPC::MTMSRD, Convert__RegGPRC1_0__Imm1_1, 0, { MCK_RegGPRC, MCK_Imm }, },
  { 6058 /* mtocrf */, PPC::MTOCRF, Convert__CRBitMask1_0__RegGPRC1_1, 0, { MCK_CRBitMask, MCK_RegGPRC }, },
  { 6065 /* mtpid */, PPC::MTSPR, Convert__imm_48__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6071 /* mtsdr1 */, PPC::MTSPR, Convert__imm_25__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6071 /* mtsdr1 */, PPC::MTSPR, Convert__imm_25__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6078 /* mtspefscr */, PPC::MTSPR, Convert__imm_512__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6088 /* mtspr */, PPC::MTSPR, Convert__Imm1_0__RegGPRC1_1, 0, { MCK_Imm, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_272__RegGPRC1_1, 0, { MCK_0, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_273__RegGPRC1_1, 0, { MCK_1, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_274__RegGPRC1_1, 0, { MCK_2, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_275__RegGPRC1_1, 0, { MCK_3, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_260__RegGPRC1_1, 0, { MCK_4, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_261__RegGPRC1_1, 0, { MCK_5, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_262__RegGPRC1_1, 0, { MCK_6, MCK_RegGPRC }, },
  { 6094 /* mtsprg */, PPC::MTSPR, Convert__imm_263__RegGPRC1_1, 0, { MCK_7, MCK_RegGPRC }, },
  { 6101 /* mtsprg0 */, PPC::MTSPR, Convert__imm_272__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6109 /* mtsprg1 */, PPC::MTSPR, Convert__imm_273__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6117 /* mtsprg2 */, PPC::MTSPR, Convert__imm_274__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6125 /* mtsprg3 */, PPC::MTSPR, Convert__imm_275__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6133 /* mtsprg4 */, PPC::MTSPR, Convert__imm_260__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6141 /* mtsprg5 */, PPC::MTSPR, Convert__imm_261__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6149 /* mtsprg6 */, PPC::MTSPR, Convert__imm_262__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6157 /* mtsprg7 */, PPC::MTSPR, Convert__imm_263__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6165 /* mtsr */, PPC::MTSR, Convert__RegGPRC1_1__U4Imm1_0, 0, { MCK_U4Imm, MCK_RegGPRC }, },
  { 6170 /* mtsrin */, PPC::MTSRIN, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6177 /* mtsrr0 */, PPC::MTSPR, Convert__imm_26__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6177 /* mtsrr0 */, PPC::MTSPR, Convert__imm_26__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6184 /* mtsrr1 */, PPC::MTSPR, Convert__imm_27__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6184 /* mtsrr1 */, PPC::MTSPR, Convert__imm_27__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6191 /* mtsrr2 */, PPC::MTSPR, Convert__imm_990__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6198 /* mtsrr3 */, PPC::MTSPR, Convert__imm_991__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6205 /* mttbhi */, PPC::MTSPR, Convert__imm_988__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6212 /* mttbl */, PPC::MTSPR, Convert__imm_284__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6218 /* mttblo */, PPC::MTSPR, Convert__imm_989__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6225 /* mttbu */, PPC::MTSPR, Convert__imm_285__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6231 /* mttcr */, PPC::MTSPR, Convert__imm_986__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6237 /* mtvscr */, PPC::MTVSCR, Convert__RegVRRC1_0, 0, { MCK_RegVRRC }, },
  { 6244 /* mtxer */, PPC::MTSPR, Convert__imm_1__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6250 /* mulhd */, PPC::MULHD, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6250 /* mulhd */, PPC::MULHDo, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6256 /* mulhdu */, PPC::MULHDU, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6256 /* mulhdu */, PPC::MULHDUo, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6263 /* mulhw */, PPC::MULHW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6263 /* mulhw */, PPC::MULHWo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6269 /* mulhwu */, PPC::MULHWU, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6269 /* mulhwu */, PPC::MULHWUo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6276 /* mulld */, PPC::MULLD, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6276 /* mulld */, PPC::MULLDo, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6282 /* mulli */, PPC::MULLI, Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 6288 /* mullw */, PPC::MULLW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6288 /* mullw */, PPC::MULLWo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6294 /* nand */, PPC::NAND, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6294 /* nand */, PPC::NANDo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6299 /* neg */, PPC::NEG, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6299 /* neg */, PPC::NEGo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6303 /* nop */, PPC::NOP, Convert_NoOperands, 0, {  }, },
  { 6307 /* nor */, PPC::NOR, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6307 /* nor */, PPC::NORo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6311 /* not */, PPC::NOR8, Convert__RegG8RC1_0__RegG8RC1_1__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6311 /* not */, PPC::NOR8o, Convert__RegG8RC1_1__RegG8RC1_2__RegG8RC1_2, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6315 /* or */, PPC::OR, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6315 /* or */, PPC::ORo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6318 /* orc */, PPC::ORC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6318 /* orc */, PPC::ORCo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6322 /* ori */, PPC::ORI, Convert__RegGPRC1_0__RegGPRC1_1__U16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 6326 /* oris */, PPC::ORIS, Convert__RegGPRC1_0__RegGPRC1_1__U16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 6331 /* popcntd */, PPC::POPCNTD, Convert__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6339 /* popcntw */, PPC::POPCNTW, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6347 /* ptesync */, PPC::SYNC, Convert__imm_2, 0, {  }, },
  { 6355 /* rfci */, PPC::RFCI, Convert_NoOperands, 0, {  }, },
  { 6360 /* rfdi */, PPC::RFDI, Convert_NoOperands, 0, {  }, },
  { 6365 /* rfi */, PPC::RFI, Convert_NoOperands, 0, {  }, },
  { 6369 /* rfid */, PPC::RFID, Convert_NoOperands, 0, {  }, },
  { 6374 /* rfmci */, PPC::RFMCI, Convert_NoOperands, 0, {  }, },
  { 6380 /* rldcl */, PPC::RLDCL, Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC, MCK_U6Imm }, },
  { 6380 /* rldcl */, PPC::RLDCLo, Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC, MCK_U6Imm }, },
  { 6386 /* rldcr */, PPC::RLDCR, Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC, MCK_U6Imm }, },
  { 6386 /* rldcr */, PPC::RLDCRo, Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC, MCK_U6Imm }, },
  { 6392 /* rldic */, PPC::RLDIC, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6392 /* rldic */, PPC::RLDICo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6398 /* rldicl */, PPC::RLDICL, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6398 /* rldicl */, PPC::RLDICLo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6405 /* rldicr */, PPC::RLDICR, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6405 /* rldicr */, PPC::RLDICRo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6412 /* rldimi */, PPC::RLDIMI, Convert__RegG8RC1_0__Tie0__RegG8RC1_1__U6Imm1_2__U6Imm1_3, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6412 /* rldimi */, PPC::RLDIMIo, Convert__RegG8RC1_1__Tie0__RegG8RC1_2__U6Imm1_3__U6Imm1_4, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm, MCK_U6Imm }, },
  { 6419 /* rlwimi */, PPC::RLWIMI, Convert__RegGPRC1_0__Tie0__RegGPRC1_1__U5Imm1_2__U5Imm1_3__U5Imm1_4, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm, MCK_U5Imm }, },
  { 6419 /* rlwimi */, PPC::RLWIMIo, Convert__RegGPRC1_1__Tie0__RegGPRC1_2__U5Imm1_3__U5Imm1_4__U5Imm1_5, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm, MCK_U5Imm }, },
  { 6426 /* rlwinm */, PPC::RLWINM, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__U5Imm1_3__U5Imm1_4, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm, MCK_U5Imm }, },
  { 6426 /* rlwinm */, PPC::RLWINMo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4__U5Imm1_5, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm, MCK_U5Imm }, },
  { 6433 /* rlwnm */, PPC::RLWNM, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__U5Imm1_4, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 6433 /* rlwnm */, PPC::RLWNMo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3__U5Imm1_4__U5Imm1_5, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm, MCK_U5Imm }, },
  { 6439 /* rotld */, PPC::RLDCL, Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2__imm_0, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6439 /* rotld */, PPC::RLDCLo, Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3__imm_0, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6445 /* rotldi */, PPC::RLDICL, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2__imm_0, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6445 /* rotldi */, PPC::RLDICLo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3__imm_0, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6452 /* rotlw */, PPC::RLWNM, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2__imm_0__imm_31, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6452 /* rotlw */, PPC::RLWNMo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3__imm_0__imm_31, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6458 /* rotlwi */, PPC::RLWINM, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2__imm_0__imm_31, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6458 /* rotlwi */, PPC::RLWINMo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3__imm_0__imm_31, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6465 /* rotrdi */, PPC::ROTRDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6465 /* rotrdi */, PPC::ROTRDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6472 /* rotrwi */, PPC::ROTRWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6472 /* rotrwi */, PPC::ROTRWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6479 /* sc */, PPC::SC, Convert__imm_0, 0, {  }, },
  { 6479 /* sc */, PPC::SC, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 6482 /* slbia */, PPC::SLBIA, Convert_NoOperands, 0, {  }, },
  { 6488 /* slbie */, PPC::SLBIE, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 6494 /* slbmfee */, PPC::SLBMFEE, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6502 /* slbmte */, PPC::SLBMTE, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6509 /* sld */, PPC::SLD, Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6509 /* sld */, PPC::SLDo, Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6513 /* sldi */, PPC::SLDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6513 /* sldi */, PPC::SLDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6518 /* slw */, PPC::SLW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6518 /* slw */, PPC::SLWo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6522 /* slwi */, PPC::SLWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6522 /* slwi */, PPC::SLWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6527 /* srad */, PPC::SRAD, Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6527 /* srad */, PPC::SRADo, Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6532 /* sradi */, PPC::SRADI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6532 /* sradi */, PPC::SRADIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6538 /* sraw */, PPC::SRAW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6538 /* sraw */, PPC::SRAWo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6543 /* srawi */, PPC::SRAWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6543 /* srawi */, PPC::SRAWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6549 /* srd */, PPC::SRD, Convert__RegG8RC1_0__RegG8RC1_1__RegGPRC1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6549 /* srd */, PPC::SRDo, Convert__RegG8RC1_1__RegG8RC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegGPRC }, },
  { 6553 /* srdi */, PPC::SRDI, Convert__RegG8RC1_0__RegG8RC1_1__U6Imm1_2, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6553 /* srdi */, PPC::SRDIo, Convert__RegG8RC1_1__RegG8RC1_2__U6Imm1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_U6Imm }, },
  { 6558 /* srw */, PPC::SRW, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6558 /* srw */, PPC::SRWo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6562 /* srwi */, PPC::SRWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6562 /* srwi */, PPC::SRWIo, Convert__RegGPRC1_1__RegGPRC1_2__U5Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6567 /* stb */, PPC::STB, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6571 /* stbcix */, PPC::STBCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6578 /* stbu */, PPC::STBU, Convert__imm_0__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6583 /* stbux */, PPC::STBUX, Convert__imm_0__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6589 /* stbx */, PPC::STBX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6594 /* std */, PPC::STD, Convert__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2, 0, { MCK_RegG8RC, MCK_DispRIX, MCK_RegGxRCNoR0 }, },
  { 6598 /* stdbrx */, PPC::STDBRX, Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6605 /* stdcix */, PPC::STDCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6612 /* stdcx */, PPC::STDCX, Convert__RegG8RC1_1__RegGxRCNoR01_2__RegGxRC1_3, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6618 /* stdu */, PPC::STDU, Convert__imm_0__RegG8RC1_0__DispRIX1_1__RegGxRCNoR01_2, 0, { MCK_RegG8RC, MCK_DispRIX, MCK_RegGxRCNoR0 }, },
  { 6623 /* stdux */, PPC::STDUX, Convert__imm_0__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6629 /* stdx */, PPC::STDX, Convert__RegG8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegG8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6634 /* stfd */, PPC::STFD, Convert__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF8RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6639 /* stfdu */, PPC::STFDU, Convert__imm_0__RegF8RC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF8RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6645 /* stfdux */, PPC::STFDUX, Convert__imm_0__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6652 /* stfdx */, PPC::STFDX, Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6658 /* stfiwx */, PPC::STFIWX, Convert__RegF8RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF8RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6665 /* stfs */, PPC::STFS, Convert__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF4RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6670 /* stfsu */, PPC::STFSU, Convert__imm_0__RegF4RC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegF4RC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6676 /* stfsux */, PPC::STFSUX, Convert__imm_0__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF4RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6683 /* stfsx */, PPC::STFSX, Convert__RegF4RC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegF4RC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6689 /* sth */, PPC::STH, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6693 /* sthbrx */, PPC::STHBRX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6700 /* sthcix */, PPC::STHCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6707 /* sthu */, PPC::STHU, Convert__imm_0__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6712 /* sthux */, PPC::STHUX, Convert__imm_0__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6718 /* sthx */, PPC::STHX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6723 /* stmw */, PPC::STMW, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6728 /* stswi */, PPC::STSWI, Convert__RegGPRC1_0__RegGPRC1_1__U5Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U5Imm }, },
  { 6734 /* stvebx */, PPC::STVEBX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6741 /* stvehx */, PPC::STVEHX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6748 /* stvewx */, PPC::STVEWX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6755 /* stvx */, PPC::STVX, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6760 /* stvxl */, PPC::STVXL, Convert__RegVRRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVRRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6766 /* stw */, PPC::STW, Convert__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6770 /* stwbrx */, PPC::STWBRX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6777 /* stwcix */, PPC::STWCIX, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6784 /* stwcx */, PPC::STWCX, Convert__RegGPRC1_1__RegGxRCNoR01_2__RegGxRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6790 /* stwu */, PPC::STWU, Convert__imm_0__RegGPRC1_0__DispRI1_1__RegGxRCNoR01_2, 0, { MCK_RegGPRC, MCK_DispRI, MCK_RegGxRCNoR0 }, },
  { 6795 /* stwux */, PPC::STWUX, Convert__imm_0__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6801 /* stwx */, PPC::STWX, Convert__RegGPRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegGPRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6806 /* stxsdx */, PPC::STXSDX, Convert__RegVSFRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSFRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6813 /* stxvd2x */, PPC::STXVD2X, Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6821 /* stxvw4x */, PPC::STXVW4X, Convert__RegVSRC1_0__RegGxRCNoR01_1__RegGxRC1_2, 0, { MCK_RegVSRC, MCK_RegGxRCNoR0, MCK_RegGxRC }, },
  { 6829 /* sub */, PPC::SUBF8, Convert__RegG8RC1_0__RegG8RC1_2__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6829 /* sub */, PPC::SUBF8o, Convert__RegG8RC1_1__RegG8RC1_3__RegG8RC1_2, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6833 /* subc */, PPC::SUBFC8, Convert__RegG8RC1_0__RegG8RC1_2__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6833 /* subc */, PPC::SUBFC8o, Convert__RegG8RC1_1__RegG8RC1_3__RegG8RC1_2, 0, { MCK__DOT_, MCK_RegG8RC, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6838 /* subf */, PPC::SUBF, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6838 /* subf */, PPC::SUBFo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6843 /* subfc */, PPC::SUBFC, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6843 /* subfc */, PPC::SUBFCo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6849 /* subfe */, PPC::SUBFE, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6849 /* subfe */, PPC::SUBFEo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6855 /* subfic */, PPC::SUBFIC, Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 6862 /* subfme */, PPC::SUBFME, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6862 /* subfme */, PPC::SUBFMEo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6869 /* subfze */, PPC::SUBFZE, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 6869 /* subfze */, PPC::SUBFZEo, Convert__RegGPRC1_1__RegGPRC1_2, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC }, },
  { 6876 /* subi */, PPC::SUBI, Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 6881 /* subic */, PPC::SUBIC, Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 6881 /* subic */, PPC::SUBICo, Convert__RegGPRC1_1__RegGPRC1_2__S16Imm1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 6887 /* subis */, PPC::SUBIS, Convert__RegGPRC1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_S16Imm }, },
  { 6893 /* sync */, PPC::SYNC, Convert__imm_0, 0, {  }, },
  { 6893 /* sync */, PPC::SYNC, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 6898 /* td */, PPC::TD, Convert__U5Imm1_0__RegG8RC1_1__RegG8RC1_2, 0, { MCK_U5Imm, MCK_RegG8RC, MCK_RegG8RC }, },
  { 6901 /* tdeq */, PPC::TD, Convert__imm_4__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6906 /* tdeqi */, PPC::TDI, Convert__imm_4__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6912 /* tdge */, PPC::TD, Convert__imm_12__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6917 /* tdgei */, PPC::TDI, Convert__imm_12__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6923 /* tdgt */, PPC::TD, Convert__imm_8__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6928 /* tdgti */, PPC::TDI, Convert__imm_8__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6934 /* tdi */, PPC::TDI, Convert__U5Imm1_0__RegG8RC1_1__S16Imm1_2, 0, { MCK_U5Imm, MCK_RegG8RC, MCK_S16Imm }, },
  { 6938 /* tdle */, PPC::TD, Convert__imm_20__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6943 /* tdlei */, PPC::TDI, Convert__imm_20__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6949 /* tdlge */, PPC::TD, Convert__imm_5__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6955 /* tdlgei */, PPC::TDI, Convert__imm_5__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6962 /* tdlgt */, PPC::TD, Convert__imm_1__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6968 /* tdlgti */, PPC::TDI, Convert__imm_1__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6975 /* tdlle */, PPC::TD, Convert__imm_6__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6981 /* tdllei */, PPC::TDI, Convert__imm_6__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 6988 /* tdllt */, PPC::TD, Convert__imm_2__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 6994 /* tdllti */, PPC::TDI, Convert__imm_2__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7001 /* tdlng */, PPC::TD, Convert__imm_6__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7007 /* tdlngi */, PPC::TDI, Convert__imm_6__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7014 /* tdlnl */, PPC::TD, Convert__imm_5__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7020 /* tdlnli */, PPC::TDI, Convert__imm_5__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7027 /* tdlt */, PPC::TD, Convert__imm_16__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7032 /* tdlti */, PPC::TDI, Convert__imm_16__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7038 /* tdne */, PPC::TD, Convert__imm_24__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7043 /* tdnei */, PPC::TDI, Convert__imm_24__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7049 /* tdng */, PPC::TD, Convert__imm_20__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7054 /* tdngi */, PPC::TDI, Convert__imm_20__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7060 /* tdnl */, PPC::TD, Convert__imm_12__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7065 /* tdnli */, PPC::TDI, Convert__imm_12__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7071 /* tdu */, PPC::TD, Convert__imm_31__RegG8RC1_0__RegG8RC1_1, 0, { MCK_RegG8RC, MCK_RegG8RC }, },
  { 7075 /* tdui */, PPC::TDI, Convert__imm_31__RegG8RC1_0__S16Imm1_1, 0, { MCK_RegG8RC, MCK_S16Imm }, },
  { 7080 /* tlbia */, PPC::TLBIA, Convert_NoOperands, 0, {  }, },
  { 7086 /* tlbie */, PPC::TLBIE, Convert__regR0__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 7086 /* tlbie */, PPC::TLBIE, Convert__RegGPRC1_1__RegGPRC1_0, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7092 /* tlbiel */, PPC::TLBIEL, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 7099 /* tlbivax */, PPC::TLBIVAX, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7107 /* tlbld */, PPC::TLBLD, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 7113 /* tlbli */, PPC::TLBLI, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 7119 /* tlbre */, PPC::TLBRE, Convert_NoOperands, 0, {  }, },
  { 7119 /* tlbre */, PPC::TLBRE2, Convert__RegGPRC1_0__RegGPRC1_1__Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_Imm }, },
  { 7125 /* tlbrehi */, PPC::TLBRE2, Convert__RegGPRC1_0__RegGPRC1_1__imm_0, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7133 /* tlbrelo */, PPC::TLBRE2, Convert__RegGPRC1_0__RegGPRC1_1__imm_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7141 /* tlbsx */, PPC::TLBSX, Convert__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7141 /* tlbsx */, PPC::TLBSX2, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 7141 /* tlbsx */, PPC::TLBSX2D, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 7147 /* tlbsync */, PPC::TLBSYNC, Convert_NoOperands, 0, {  }, },
  { 7155 /* tlbwe */, PPC::TLBWE, Convert_NoOperands, 0, {  }, },
  { 7155 /* tlbwe */, PPC::TLBWE2, Convert__RegGPRC1_0__RegGPRC1_1__Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_Imm }, },
  { 7161 /* tlbwehi */, PPC::TLBWE2, Convert__RegGPRC1_0__RegGPRC1_1__imm_0, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7169 /* tlbwelo */, PPC::TLBWE2, Convert__RegGPRC1_0__RegGPRC1_1__imm_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7177 /* trap */, PPC::TRAP, Convert_NoOperands, 0, {  }, },
  { 7182 /* tw */, PPC::TW, Convert__U5Imm1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_U5Imm, MCK_RegGPRC, MCK_RegGPRC }, },
  { 7185 /* tweq */, PPC::TW, Convert__imm_4__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7190 /* tweqi */, PPC::TWI, Convert__imm_4__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7196 /* twge */, PPC::TW, Convert__imm_12__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7201 /* twgei */, PPC::TWI, Convert__imm_12__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7207 /* twgt */, PPC::TW, Convert__imm_8__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7212 /* twgti */, PPC::TWI, Convert__imm_8__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7218 /* twi */, PPC::TWI, Convert__U5Imm1_0__RegGPRC1_1__S16Imm1_2, 0, { MCK_U5Imm, MCK_RegGPRC, MCK_S16Imm }, },
  { 7222 /* twle */, PPC::TW, Convert__imm_20__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7227 /* twlei */, PPC::TWI, Convert__imm_20__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7233 /* twlge */, PPC::TW, Convert__imm_5__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7239 /* twlgei */, PPC::TWI, Convert__imm_5__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7246 /* twlgt */, PPC::TW, Convert__imm_1__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7252 /* twlgti */, PPC::TWI, Convert__imm_1__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7259 /* twlle */, PPC::TW, Convert__imm_6__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7265 /* twllei */, PPC::TWI, Convert__imm_6__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7272 /* twllt */, PPC::TW, Convert__imm_2__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7278 /* twllti */, PPC::TWI, Convert__imm_2__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7285 /* twlng */, PPC::TW, Convert__imm_6__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7291 /* twlngi */, PPC::TWI, Convert__imm_6__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7298 /* twlnl */, PPC::TW, Convert__imm_5__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7304 /* twlnli */, PPC::TWI, Convert__imm_5__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7311 /* twlt */, PPC::TW, Convert__imm_16__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7316 /* twlti */, PPC::TWI, Convert__imm_16__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7322 /* twne */, PPC::TW, Convert__imm_24__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7327 /* twnei */, PPC::TWI, Convert__imm_24__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7333 /* twng */, PPC::TW, Convert__imm_20__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7338 /* twngi */, PPC::TWI, Convert__imm_20__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7344 /* twnl */, PPC::TW, Convert__imm_12__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7349 /* twnli */, PPC::TWI, Convert__imm_12__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7355 /* twu */, PPC::TW, Convert__imm_31__RegGPRC1_0__RegGPRC1_1, 0, { MCK_RegGPRC, MCK_RegGPRC }, },
  { 7359 /* twui */, PPC::TWI, Convert__imm_31__RegGPRC1_0__S16Imm1_1, 0, { MCK_RegGPRC, MCK_S16Imm }, },
  { 7364 /* vaddcuw */, PPC::VADDCUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7372 /* vaddfp */, PPC::VADDFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7379 /* vaddsbs */, PPC::VADDSBS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7387 /* vaddshs */, PPC::VADDSHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7395 /* vaddsws */, PPC::VADDSWS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7403 /* vaddubm */, PPC::VADDUBM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7411 /* vaddubs */, PPC::VADDUBS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7419 /* vadduhm */, PPC::VADDUHM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7427 /* vadduhs */, PPC::VADDUHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7435 /* vadduwm */, PPC::VADDUWM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7443 /* vadduws */, PPC::VADDUWS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7451 /* vand */, PPC::VAND, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7456 /* vandc */, PPC::VANDC, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7462 /* vavgsb */, PPC::VAVGSB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7469 /* vavgsh */, PPC::VAVGSH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7476 /* vavgsw */, PPC::VAVGSW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7483 /* vavgub */, PPC::VAVGUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7490 /* vavguh */, PPC::VAVGUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7497 /* vavguw */, PPC::VAVGUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7504 /* vcfsx */, PPC::VCFSX, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 7510 /* vcfux */, PPC::VCFUX, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 7516 /* vcmpbfp */, PPC::VCMPBFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7516 /* vcmpbfp */, PPC::VCMPBFPo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7524 /* vcmpeqfp */, PPC::VCMPEQFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7524 /* vcmpeqfp */, PPC::VCMPEQFPo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7533 /* vcmpequb */, PPC::VCMPEQUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7533 /* vcmpequb */, PPC::VCMPEQUBo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7542 /* vcmpequh */, PPC::VCMPEQUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7542 /* vcmpequh */, PPC::VCMPEQUHo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7551 /* vcmpequw */, PPC::VCMPEQUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7551 /* vcmpequw */, PPC::VCMPEQUWo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7560 /* vcmpgefp */, PPC::VCMPGEFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7560 /* vcmpgefp */, PPC::VCMPGEFPo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7569 /* vcmpgtfp */, PPC::VCMPGTFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7569 /* vcmpgtfp */, PPC::VCMPGTFPo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7578 /* vcmpgtsb */, PPC::VCMPGTSB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7578 /* vcmpgtsb */, PPC::VCMPGTSBo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7587 /* vcmpgtsh */, PPC::VCMPGTSH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7587 /* vcmpgtsh */, PPC::VCMPGTSHo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7596 /* vcmpgtsw */, PPC::VCMPGTSW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7596 /* vcmpgtsw */, PPC::VCMPGTSWo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7605 /* vcmpgtub */, PPC::VCMPGTUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7605 /* vcmpgtub */, PPC::VCMPGTUBo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7614 /* vcmpgtuh */, PPC::VCMPGTUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7614 /* vcmpgtuh */, PPC::VCMPGTUHo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7623 /* vcmpgtuw */, PPC::VCMPGTUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7623 /* vcmpgtuw */, PPC::VCMPGTUWo, Convert__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK__DOT_, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7632 /* vctsxs */, PPC::VCTSXS, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 7639 /* vctuxs */, PPC::VCTUXS, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 7646 /* vexptefp */, PPC::VEXPTEFP, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 7655 /* vlogefp */, PPC::VLOGEFP, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 7663 /* vmaddfp */, PPC::VMADDFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7671 /* vmaxfp */, PPC::VMAXFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7678 /* vmaxsb */, PPC::VMAXSB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7685 /* vmaxsh */, PPC::VMAXSH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7692 /* vmaxsw */, PPC::VMAXSW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7699 /* vmaxub */, PPC::VMAXUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7706 /* vmaxuh */, PPC::VMAXUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7713 /* vmaxuw */, PPC::VMAXUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7720 /* vmhaddshs */, PPC::VMHADDSHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7730 /* vmhraddshs */, PPC::VMHRADDSHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7741 /* vminfp */, PPC::VMINFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7748 /* vminsb */, PPC::VMINSB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7755 /* vminsh */, PPC::VMINSH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7762 /* vminsw */, PPC::VMINSW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7769 /* vminub */, PPC::VMINUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7776 /* vminuh */, PPC::VMINUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7783 /* vminuw */, PPC::VMINUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7790 /* vmladduhm */, PPC::VMLADDUHM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7800 /* vmrghb */, PPC::VMRGHB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7807 /* vmrghh */, PPC::VMRGHH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7814 /* vmrghw */, PPC::VMRGHW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7821 /* vmrglb */, PPC::VMRGLB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7828 /* vmrglh */, PPC::VMRGLH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7835 /* vmrglw */, PPC::VMRGLW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7842 /* vmsummbm */, PPC::VMSUMMBM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7851 /* vmsumshm */, PPC::VMSUMSHM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7860 /* vmsumshs */, PPC::VMSUMSHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7869 /* vmsumubm */, PPC::VMSUMUBM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7878 /* vmsumuhm */, PPC::VMSUMUHM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7887 /* vmsumuhs */, PPC::VMSUMUHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7896 /* vmulesb */, PPC::VMULESB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7904 /* vmulesh */, PPC::VMULESH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7912 /* vmuleub */, PPC::VMULEUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7920 /* vmuleuh */, PPC::VMULEUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7928 /* vmulosb */, PPC::VMULOSB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7936 /* vmulosh */, PPC::VMULOSH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7944 /* vmuloub */, PPC::VMULOUB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7952 /* vmulouh */, PPC::VMULOUH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7960 /* vnmsubfp */, PPC::VNMSUBFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7969 /* vnor */, PPC::VNOR, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7974 /* vor */, PPC::VOR, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7978 /* vperm */, PPC::VPERM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7984 /* vpkpx */, PPC::VPKPX, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7990 /* vpkshss */, PPC::VPKSHSS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 7998 /* vpkshus */, PPC::VPKSHUS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8006 /* vpkswss */, PPC::VPKSWSS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8014 /* vpkswus */, PPC::VPKSWUS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8022 /* vpkuhum */, PPC::VPKUHUM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8030 /* vpkuhus */, PPC::VPKUHUS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8038 /* vpkuwum */, PPC::VPKUWUM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8046 /* vpkuwus */, PPC::VPKUWUS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8054 /* vrefp */, PPC::VREFP, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8060 /* vrfim */, PPC::VRFIM, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8066 /* vrfin */, PPC::VRFIN, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8072 /* vrfip */, PPC::VRFIP, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8078 /* vrfiz */, PPC::VRFIZ, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8084 /* vrlb */, PPC::VRLB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8089 /* vrlh */, PPC::VRLH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8094 /* vrlw */, PPC::VRLW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8099 /* vrsqrtefp */, PPC::VRSQRTEFP, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8109 /* vsel */, PPC::VSEL, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__RegVRRC1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8114 /* vsl */, PPC::VSL, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8118 /* vslb */, PPC::VSLB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8123 /* vsldoi */, PPC::VSLDOI, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2__U5Imm1_3, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 8130 /* vslh */, PPC::VSLH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8135 /* vslo */, PPC::VSLO, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8140 /* vslw */, PPC::VSLW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8145 /* vspltb */, PPC::VSPLTB, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 8152 /* vsplth */, PPC::VSPLTH, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 8159 /* vspltisb */, PPC::VSPLTISB, Convert__RegVRRC1_0__S5Imm1_1, 0, { MCK_RegVRRC, MCK_S5Imm }, },
  { 8168 /* vspltish */, PPC::VSPLTISH, Convert__RegVRRC1_0__S5Imm1_1, 0, { MCK_RegVRRC, MCK_S5Imm }, },
  { 8177 /* vspltisw */, PPC::VSPLTISW, Convert__RegVRRC1_0__S5Imm1_1, 0, { MCK_RegVRRC, MCK_S5Imm }, },
  { 8186 /* vspltw */, PPC::VSPLTW, Convert__RegVRRC1_0__U5Imm1_2__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_U5Imm }, },
  { 8193 /* vsr */, PPC::VSR, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8197 /* vsrab */, PPC::VSRAB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8203 /* vsrah */, PPC::VSRAH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8209 /* vsraw */, PPC::VSRAW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8215 /* vsrb */, PPC::VSRB, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8220 /* vsrh */, PPC::VSRH, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8225 /* vsro */, PPC::VSRO, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8230 /* vsrw */, PPC::VSRW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8235 /* vsubcuw */, PPC::VSUBCUW, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8243 /* vsubfp */, PPC::VSUBFP, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8250 /* vsubsbs */, PPC::VSUBSBS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8258 /* vsubshs */, PPC::VSUBSHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8266 /* vsubsws */, PPC::VSUBSWS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8274 /* vsububm */, PPC::VSUBUBM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8282 /* vsububs */, PPC::VSUBUBS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8290 /* vsubuhm */, PPC::VSUBUHM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8298 /* vsubuhs */, PPC::VSUBUHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8306 /* vsubuwm */, PPC::VSUBUWM, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8314 /* vsubuws */, PPC::VSUBUWS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8322 /* vsum2sws */, PPC::VSUM2SWS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8331 /* vsum4sbs */, PPC::VSUM4SBS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8340 /* vsum4shs */, PPC::VSUM4SHS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8349 /* vsum4ubs */, PPC::VSUM4UBS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8358 /* vsumsws */, PPC::VSUMSWS, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8366 /* vupkhpx */, PPC::VUPKHPX, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8374 /* vupkhsb */, PPC::VUPKHSB, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8382 /* vupkhsh */, PPC::VUPKHSH, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8390 /* vupklpx */, PPC::VUPKLPX, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8398 /* vupklsb */, PPC::VUPKLSB, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8406 /* vupklsh */, PPC::VUPKLSH, Convert__RegVRRC1_0__RegVRRC1_1, 0, { MCK_RegVRRC, MCK_RegVRRC }, },
  { 8414 /* vxor */, PPC::VXOR, Convert__RegVRRC1_0__RegVRRC1_1__RegVRRC1_2, 0, { MCK_RegVRRC, MCK_RegVRRC, MCK_RegVRRC }, },
  { 8419 /* wait */, PPC::WAIT, Convert__imm_0, 0, {  }, },
  { 8419 /* wait */, PPC::WAIT, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 8424 /* waitimpl */, PPC::WAIT, Convert__imm_2, 0, {  }, },
  { 8433 /* waitrsv */, PPC::WAIT, Convert__imm_1, 0, {  }, },
  { 8441 /* wrtee */, PPC::WRTEE, Convert__RegGPRC1_0, 0, { MCK_RegGPRC }, },
  { 8447 /* wrteei */, PPC::WRTEEI, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 8454 /* xnop */, PPC::XORI, Convert__regR0__regR0__imm_0, 0, {  }, },
  { 8459 /* xor */, PPC::XOR, Convert__RegGPRC1_0__RegGPRC1_1__RegGPRC1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 8459 /* xor */, PPC::XORo, Convert__RegGPRC1_1__RegGPRC1_2__RegGPRC1_3, 0, { MCK__DOT_, MCK_RegGPRC, MCK_RegGPRC, MCK_RegGPRC }, },
  { 8463 /* xori */, PPC::XORI, Convert__RegGPRC1_0__RegGPRC1_1__U16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 8468 /* xoris */, PPC::XORIS, Convert__RegGPRC1_0__RegGPRC1_1__U16Imm1_2, 0, { MCK_RegGPRC, MCK_RegGPRC, MCK_U16Imm }, },
  { 8474 /* xsabsdp */, PPC::XSABSDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8482 /* xsadddp */, PPC::XSADDDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8490 /* xscmpodp */, PPC::XSCMPODP, Convert__RegCRRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegCRRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8499 /* xscmpudp */, PPC::XSCMPUDP, Convert__RegCRRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegCRRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8508 /* xscpsgndp */, PPC::XSCPSGNDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8518 /* xscvdpsp */, PPC::XSCVDPSP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8527 /* xscvdpsxds */, PPC::XSCVDPSXDS, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8538 /* xscvdpsxws */, PPC::XSCVDPSXWS, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8549 /* xscvdpuxds */, PPC::XSCVDPUXDS, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8560 /* xscvdpuxws */, PPC::XSCVDPUXWS, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8571 /* xscvspdp */, PPC::XSCVSPDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8580 /* xscvsxddp */, PPC::XSCVSXDDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8590 /* xscvuxddp */, PPC::XSCVUXDDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8600 /* xsdivdp */, PPC::XSDIVDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8608 /* xsmaddadp */, PPC::XSMADDADP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8618 /* xsmaddmdp */, PPC::XSMADDMDP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8628 /* xsmaxdp */, PPC::XSMAXDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8636 /* xsmindp */, PPC::XSMINDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8644 /* xsmsubadp */, PPC::XSMSUBADP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8654 /* xsmsubmdp */, PPC::XSMSUBMDP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8664 /* xsmuldp */, PPC::XSMULDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8672 /* xsnabsdp */, PPC::XSNABSDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8681 /* xsnegdp */, PPC::XSNEGDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8689 /* xsnmaddadp */, PPC::XSNMADDADP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8700 /* xsnmaddmdp */, PPC::XSNMADDMDP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8711 /* xsnmsubadp */, PPC::XSNMSUBADP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8722 /* xsnmsubmdp */, PPC::XSNMSUBMDP, Convert__RegVSFRC1_0__Tie0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8733 /* xsrdpi */, PPC::XSRDPI, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8740 /* xsrdpic */, PPC::XSRDPIC, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8748 /* xsrdpim */, PPC::XSRDPIM, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8756 /* xsrdpip */, PPC::XSRDPIP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8764 /* xsrdpiz */, PPC::XSRDPIZ, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8772 /* xsredp */, PPC::XSREDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8779 /* xsrsqrtedp */, PPC::XSRSQRTEDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8790 /* xssqrtdp */, PPC::XSSQRTDP, Convert__RegVSFRC1_0__RegVSFRC1_1, 0, { MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8799 /* xssubdp */, PPC::XSSUBDP, Convert__RegVSFRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegVSFRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8807 /* xstdivdp */, PPC::XSTDIVDP, Convert__RegCRRC1_0__RegVSFRC1_1__RegVSFRC1_2, 0, { MCK_RegCRRC, MCK_RegVSFRC, MCK_RegVSFRC }, },
  { 8816 /* xstsqrtdp */, PPC::XSTSQRTDP, Convert__RegCRRC1_0__RegVSFRC1_1, 0, { MCK_RegCRRC, MCK_RegVSFRC }, },
  { 8826 /* xvabsdp */, PPC::XVABSDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8834 /* xvabssp */, PPC::XVABSSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8842 /* xvadddp */, PPC::XVADDDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8850 /* xvaddsp */, PPC::XVADDSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8858 /* xvcmpeqdp */, PPC::XVCMPEQDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8858 /* xvcmpeqdp */, PPC::XVCMPEQDPo, Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK__DOT_, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8868 /* xvcmpeqsp */, PPC::XVCMPEQSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8868 /* xvcmpeqsp */, PPC::XVCMPEQSPo, Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK__DOT_, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8878 /* xvcmpgedp */, PPC::XVCMPGEDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8878 /* xvcmpgedp */, PPC::XVCMPGEDPo, Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK__DOT_, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8888 /* xvcmpgesp */, PPC::XVCMPGESP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8888 /* xvcmpgesp */, PPC::XVCMPGESPo, Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK__DOT_, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8898 /* xvcmpgtdp */, PPC::XVCMPGTDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8898 /* xvcmpgtdp */, PPC::XVCMPGTDPo, Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK__DOT_, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8908 /* xvcmpgtsp */, PPC::XVCMPGTSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8908 /* xvcmpgtsp */, PPC::XVCMPGTSPo, Convert__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK__DOT_, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8918 /* xvcpsgndp */, PPC::XVCPSGNDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8928 /* xvcpsgnsp */, PPC::XVCPSGNSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 8938 /* xvcvdpsp */, PPC::XVCVDPSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8947 /* xvcvdpsxds */, PPC::XVCVDPSXDS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8958 /* xvcvdpsxws */, PPC::XVCVDPSXWS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8969 /* xvcvdpuxds */, PPC::XVCVDPUXDS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8980 /* xvcvdpuxws */, PPC::XVCVDPUXWS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 8991 /* xvcvspdp */, PPC::XVCVSPDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9000 /* xvcvspsxds */, PPC::XVCVSPSXDS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9011 /* xvcvspsxws */, PPC::XVCVSPSXWS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9022 /* xvcvspuxds */, PPC::XVCVSPUXDS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9033 /* xvcvspuxws */, PPC::XVCVSPUXWS, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9044 /* xvcvsxddp */, PPC::XVCVSXDDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9054 /* xvcvsxdsp */, PPC::XVCVSXDSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9064 /* xvcvsxwdp */, PPC::XVCVSXWDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9074 /* xvcvsxwsp */, PPC::XVCVSXWSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9084 /* xvcvuxddp */, PPC::XVCVUXDDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9094 /* xvcvuxdsp */, PPC::XVCVUXDSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9104 /* xvcvuxwdp */, PPC::XVCVUXWDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9114 /* xvcvuxwsp */, PPC::XVCVUXWSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9124 /* xvdivdp */, PPC::XVDIVDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9132 /* xvdivsp */, PPC::XVDIVSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9140 /* xvmaddadp */, PPC::XVMADDADP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9150 /* xvmaddasp */, PPC::XVMADDASP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9160 /* xvmaddmdp */, PPC::XVMADDMDP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9170 /* xvmaddmsp */, PPC::XVMADDMSP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9180 /* xvmaxdp */, PPC::XVMAXDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9188 /* xvmaxsp */, PPC::XVMAXSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9196 /* xvmindp */, PPC::XVMINDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9204 /* xvminsp */, PPC::XVMINSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9212 /* xvmovdp */, PPC::XVCPSGNDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9220 /* xvmovsp */, PPC::XVCPSGNSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9228 /* xvmsubadp */, PPC::XVMSUBADP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9238 /* xvmsubasp */, PPC::XVMSUBASP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9248 /* xvmsubmdp */, PPC::XVMSUBMDP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9258 /* xvmsubmsp */, PPC::XVMSUBMSP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9268 /* xvmuldp */, PPC::XVMULDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9276 /* xvmulsp */, PPC::XVMULSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9284 /* xvnabsdp */, PPC::XVNABSDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9293 /* xvnabssp */, PPC::XVNABSSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9302 /* xvnegdp */, PPC::XVNEGDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9310 /* xvnegsp */, PPC::XVNEGSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9318 /* xvnmaddadp */, PPC::XVNMADDADP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9329 /* xvnmaddasp */, PPC::XVNMADDASP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9340 /* xvnmaddmdp */, PPC::XVNMADDMDP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9351 /* xvnmaddmsp */, PPC::XVNMADDMSP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9362 /* xvnmsubadp */, PPC::XVNMSUBADP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9373 /* xvnmsubasp */, PPC::XVNMSUBASP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9384 /* xvnmsubmdp */, PPC::XVNMSUBMDP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9395 /* xvnmsubmsp */, PPC::XVNMSUBMSP, Convert__RegVSRC1_0__Tie0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9406 /* xvrdpi */, PPC::XVRDPI, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9413 /* xvrdpic */, PPC::XVRDPIC, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9421 /* xvrdpim */, PPC::XVRDPIM, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9429 /* xvrdpip */, PPC::XVRDPIP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9437 /* xvrdpiz */, PPC::XVRDPIZ, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9445 /* xvredp */, PPC::XVREDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9452 /* xvresp */, PPC::XVRESP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9459 /* xvrspi */, PPC::XVRSPI, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9466 /* xvrspic */, PPC::XVRSPIC, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9474 /* xvrspim */, PPC::XVRSPIM, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9482 /* xvrspip */, PPC::XVRSPIP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9490 /* xvrspiz */, PPC::XVRSPIZ, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9498 /* xvrsqrtedp */, PPC::XVRSQRTEDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9509 /* xvrsqrtesp */, PPC::XVRSQRTESP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9520 /* xvsqrtdp */, PPC::XVSQRTDP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9529 /* xvsqrtsp */, PPC::XVSQRTSP, Convert__RegVSRC1_0__RegVSRC1_1, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
  { 9538 /* xvsubdp */, PPC::XVSUBDP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9546 /* xvsubsp */, PPC::XVSUBSP, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9554 /* xvtdivdp */, PPC::XVTDIVDP, Convert__RegCRRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegCRRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9563 /* xvtdivsp */, PPC::XVTDIVSP, Convert__RegCRRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegCRRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9572 /* xvtsqrtdp */, PPC::XVTSQRTDP, Convert__RegCRRC1_0__RegVSRC1_1, 0, { MCK_RegCRRC, MCK_RegVSRC }, },
  { 9582 /* xvtsqrtsp */, PPC::XVTSQRTSP, Convert__RegCRRC1_0__RegVSRC1_1, 0, { MCK_RegCRRC, MCK_RegVSRC }, },
  { 9592 /* xxland */, PPC::XXLAND, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9599 /* xxlandc */, PPC::XXLANDC, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9607 /* xxlnor */, PPC::XXLNOR, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9614 /* xxlor */, PPC::XXLOR, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9620 /* xxlxor */, PPC::XXLXOR, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9627 /* xxmrghd */, PPC::XXPERMDI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__imm_0, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9635 /* xxmrghw */, PPC::XXMRGHW, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9643 /* xxmrgld */, PPC::XXPERMDI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__imm_3, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9651 /* xxmrglw */, PPC::XXMRGLW, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9659 /* xxpermdi */, PPC::XXPERMDI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__U2Imm1_3, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC, MCK_U2Imm }, },
  { 9668 /* xxsel */, PPC::XXSEL, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__RegVSRC1_3, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC }, },
  { 9674 /* xxsldwi */, PPC::XXSLDWI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_2__U2Imm1_3, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_RegVSRC, MCK_U2Imm }, },
  { 9682 /* xxspltd */, PPC::XXPERMDI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_0, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_0 }, },
  { 9682 /* xxspltd */, PPC::XXPERMDI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_3, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_1 }, },
  { 9690 /* xxspltw */, PPC::XXSPLTW, Convert__RegVSRC1_0__RegVSRC1_1__U2Imm1_2, 0, { MCK_RegVSRC, MCK_RegVSRC, MCK_U2Imm }, },
  { 9698 /* xxswapd */, PPC::XXPERMDI, Convert__RegVSRC1_0__RegVSRC1_1__RegVSRC1_1__imm_2, 0, { MCK_RegVSRC, MCK_RegVSRC }, },
};

bool PPCAsmParser::
mnemonicIsValid(StringRef Mnemonic, unsigned VariantID) {
  // Find the appropriate table for this asm variant.
  const MatchEntry *Start, *End;
  switch (VariantID) {
  default: llvm_unreachable("invalid variant!");
  case 0: Start = std::begin(MatchTable0); End = std::end(MatchTable0); break;
  }
  // Search the table.
  std::pair<const MatchEntry*, const MatchEntry*> MnemonicRange =
    std::equal_range(Start, End, Mnemonic, LessOpcode());
  return MnemonicRange.first != MnemonicRange.second;
}

unsigned PPCAsmParser::
MatchInstructionImpl(const OperandVector &Operands,
                     MCInst &Inst, uint64_t &ErrorInfo,
                     bool matchingInlineAsm, unsigned VariantID) {
  // Eliminate obvious mismatches.
  if (Operands.size() > 7) {
    ErrorInfo = 7;
    return Match_InvalidOperand;
  }

  // Get the current feature set.
  uint64_t AvailableFeatures = getAvailableFeatures();

  // Get the instruction mnemonic, which is the first token.
  StringRef Mnemonic = ((PPCOperand&)*Operands[0]).getToken();

  // Some state to try to produce better error messages.
  bool HadMatchOtherThanFeatures = false;
  bool HadMatchOtherThanPredicate = false;
  unsigned RetCode = Match_InvalidOperand;
  uint64_t MissingFeatures = ~0ULL;
  // Set ErrorInfo to the operand that mismatches if it is
  // wrong for all instances of the instruction.
  ErrorInfo = ~0U;
  // Find the appropriate table for this asm variant.
  const MatchEntry *Start, *End;
  switch (VariantID) {
  default: llvm_unreachable("invalid variant!");
  case 0: Start = std::begin(MatchTable0); End = std::end(MatchTable0); break;
  }
  // Search the table.
  std::pair<const MatchEntry*, const MatchEntry*> MnemonicRange =
    std::equal_range(Start, End, Mnemonic, LessOpcode());

  // Return a more specific error code if no mnemonics match.
  if (MnemonicRange.first == MnemonicRange.second)
    return Match_MnemonicFail;

  for (const MatchEntry *it = MnemonicRange.first, *ie = MnemonicRange.second;
       it != ie; ++it) {
    // equal_range guarantees that instruction mnemonic matches.
    assert(Mnemonic == it->getMnemonic());
    bool OperandsValid = true;
    for (unsigned i = 0; i != 6; ++i) {
      if (i + 1 >= Operands.size()) {
        OperandsValid = (it->Classes[i] == InvalidMatchClass);
        if (!OperandsValid) ErrorInfo = i + 1;
        break;
      }
      unsigned Diag = validateOperandClass(*Operands[i+1],
                                           (MatchClassKind)it->Classes[i]);
      if (Diag == Match_Success)
        continue;
      // If the generic handler indicates an invalid operand
      // failure, check for a special case.
      if (Diag == Match_InvalidOperand) {
        Diag = validateTargetOperandClass(*Operands[i+1],
                                           (MatchClassKind)it->Classes[i]);
        if (Diag == Match_Success)
          continue;
      }
      // If this operand is broken for all of the instances of this
      // mnemonic, keep track of it so we can report loc info.
      // If we already had a match that only failed due to a
      // target predicate, that diagnostic is preferred.
      if (!HadMatchOtherThanPredicate &&
          (it == MnemonicRange.first || ErrorInfo <= i+1)) {
        ErrorInfo = i+1;
        // InvalidOperand is the default. Prefer specificity.
        if (Diag != Match_InvalidOperand)
          RetCode = Diag;
      }
      // Otherwise, just reject this instance of the mnemonic.
      OperandsValid = false;
      break;
    }

    if (!OperandsValid) continue;
    if ((AvailableFeatures & it->RequiredFeatures) != it->RequiredFeatures) {
      HadMatchOtherThanFeatures = true;
      uint64_t NewMissingFeatures = it->RequiredFeatures & ~AvailableFeatures;
      if (CountPopulation_64(NewMissingFeatures) <=
          CountPopulation_64(MissingFeatures))
        MissingFeatures = NewMissingFeatures;
      continue;
    }

    Inst.clear();

    if (matchingInlineAsm) {
      Inst.setOpcode(it->Opcode);
      convertToMapAndConstraints(it->ConvertFn, Operands);
      return Match_Success;
    }

    // We have selected a definite instruction, convert the parsed
    // operands into the appropriate MCInst.
    convertToMCInst(it->ConvertFn, Inst, it->Opcode, Operands);

    // We have a potential match. Check the target predicate to
    // handle any context sensitive constraints.
    unsigned MatchResult;
    if ((MatchResult = checkTargetMatchPredicate(Inst)) != Match_Success) {
      Inst.clear();
      RetCode = MatchResult;
      HadMatchOtherThanPredicate = true;
      continue;
    }

    std::string Info;
    if (MII.get(Inst.getOpcode()).getDeprecatedInfo(Inst, STI, Info)) {
      SMLoc Loc = ((PPCOperand&)*Operands[0]).getStartLoc();
      getParser().Warning(Loc, Info, None);
    }
    return Match_Success;
  }

  // Okay, we had no match.  Try to return a useful error code.
  if (HadMatchOtherThanPredicate || !HadMatchOtherThanFeatures)
    return RetCode;

  // Missing feature matches return which features were missing
  ErrorInfo = MissingFeatures;
  return Match_MissingFeature;
}

#endif // GET_MATCHER_IMPLEMENTATION

