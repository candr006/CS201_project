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

  enum OperandMatchResultTy {
    MatchOperand_Success,    // operand matched successfully
    MatchOperand_NoMatch,    // operand did not match
    MatchOperand_ParseFail   // operand matched but had errors
  };
  OperandMatchResultTy MatchOperandParserImpl(
    OperandVector &Operands,
    StringRef Mnemonic);
  OperandMatchResultTy tryCustomParseOperand(
    OperandVector &Operands,
    unsigned MCK);

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
  CVT_95_addImmOperands,
  CVT_imm_0,
  CVT_NUM_CONVERTERS
};

enum InstructionConversionKind {
  Convert_NoOperands,
  Convert__Imm1_0,
  Convert__Imm1_0__imm_0,
  Convert__SWaitCnt1_0,
  CVT_NUM_SIGNATURES
};

} // end anonymous namespace

static const uint8_t ConversionTable[CVT_NUM_SIGNATURES][5] = {
  // Convert_NoOperands
  { CVT_Done },
  // Convert__Imm1_0
  { CVT_95_addImmOperands, 1, CVT_Done },
  // Convert__Imm1_0__imm_0
  { CVT_95_addImmOperands, 1, CVT_imm_0, 0, CVT_Done },
  // Convert__SWaitCnt1_0
  { CVT_95_addImmOperands, 1, CVT_Done },
};

void AMDGPUAsmParser::
convertToMCInst(unsigned Kind, MCInst &Inst, unsigned Opcode,
                const OperandVector &Operands) {
  assert(Kind < CVT_NUM_SIGNATURES && "Invalid signature!");
  const uint8_t *Converter = ConversionTable[Kind];
  Inst.setOpcode(Opcode);
  for (const uint8_t *p = Converter; *p; p+= 2) {
    switch (*p) {
    default: llvm_unreachable("invalid conversion entry!");
    case CVT_Reg:
      static_cast<AMDGPUOperand&>(*Operands[*(p + 1)]).addRegOperands(Inst, 1);
      break;
    case CVT_Tied:
      Inst.addOperand(Inst.getOperand(*(p + 1)));
      break;
    case CVT_95_addImmOperands:
      static_cast<AMDGPUOperand&>(*Operands[*(p + 1)]).addImmOperands(Inst, 1);
      break;
    case CVT_imm_0:
      Inst.addOperand(MCOperand::CreateImm(0));
      break;
    }
  }
}

void AMDGPUAsmParser::
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
    case CVT_95_addImmOperands:
      Operands[*(p + 1)]->setMCOperandNum(NumMCOperands);
      Operands[*(p + 1)]->setConstraint("m");
      NumMCOperands += 1;
      break;
    case CVT_imm_0:
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
  MCK_R600_TReg32_X, // register class 'R600_TReg32_X'
  MCK_R600_TReg32_Y, // register class 'R600_TReg32_Y'
  MCK_R600_TReg32_Z, // register class 'R600_TReg32_Z'
  MCK_R600_TReg32_W, // register class 'R600_TReg32_W'
  MCK_R600_TReg32, // register class 'R600_TReg32'
  MCK_R600_Addr, // register class 'R600_Addr'
  MCK_R600_KC1_X, // register class 'R600_KC1_X'
  MCK_R600_KC1_Y, // register class 'R600_KC1_Y'
  MCK_R600_KC1_Z, // register class 'R600_KC1_Z'
  MCK_R600_KC1_W, // register class 'R600_KC1_W'
  MCK_R600_KC1, // register class 'R600_KC1'
  MCK_R600_ArrayBase, // register class 'R600_ArrayBase'
  MCK_Reg34, // derived register class
  MCK_R600_LDS_SRC_REG, // register class 'R600_LDS_SRC_REG'
  MCK_R600_Reg32, // register class 'R600_Reg32'
  MCK_R600_Addr_Y, // register class 'R600_Addr_Y'
  MCK_R600_Addr_Z, // register class 'R600_Addr_Z'
  MCK_R600_Addr_W, // register class 'R600_Addr_W'
  MCK_R600_Reg128, // register class 'R600_Reg128'
  MCK_R600_Reg64, // register class 'R600_Reg64'
  MCK_Reg12, // derived register class
  MCK_Reg14, // derived register class
  MCK_Reg15, // derived register class
  MCK_Reg16, // derived register class
  MCK_R600_Reg128Vertical, // register class 'R600_Reg128Vertical'
  MCK_Reg18, // derived register class
  MCK_Reg19, // derived register class
  MCK_Reg20, // derived register class
  MCK_Reg21, // derived register class
  MCK_R600_Reg64Vertical, // register class 'R600_Reg64Vertical'
  MCK_R600_KC0_X, // register class 'R600_KC0_X'
  MCK_R600_KC0_Y, // register class 'R600_KC0_Y'
  MCK_R600_KC0_Z, // register class 'R600_KC0_Z'
  MCK_R600_KC0_W, // register class 'R600_KC0_W'
  MCK_R600_KC0, // register class 'R600_KC0'
  MCK_R600_Predicate_Bit, // register class 'R600_Predicate_Bit'
  MCK_R600_Predicate, // register class 'R600_Predicate'
  MCK_SReg_32, // register class 'SReg_32'
  MCK_VS_32, // register class 'VS_32'
  MCK_VCCReg, // register class 'VCCReg'
  MCK_EXECReg, // register class 'EXECReg'
  MCK_SReg_64, // register class 'SReg_64'
  MCK_VS_64, // register class 'VS_64'
  MCK_SCCReg, // register class 'SCCReg'
  MCK_M0Reg, // register class 'M0Reg'
  MCK_SGPR_32, // register class 'SGPR_32'
  MCK_VReg_1, // register class 'VReg_1,VGPR_32'
  MCK_SReg_128, // register class 'SReg_128'
  MCK_VSrc_128, // register class 'VSrc_128'
  MCK_SReg_256, // register class 'SReg_256'
  MCK_SReg_512, // register class 'SReg_512'
  MCK_SGPR_64, // register class 'SGPR_64'
  MCK_VReg_128, // register class 'VReg_128'
  MCK_VReg_256, // register class 'VReg_256'
  MCK_VReg_512, // register class 'VReg_512'
  MCK_VReg_64, // register class 'VReg_64'
  MCK_VReg_96, // register class 'VReg_96'
  MCK_Imm, // user defined class 'ImmAsmOperand'
  MCK_SWaitCnt, // user defined class 'SWaitMatchClass'
  NumMatchClassKinds
};

}

static MatchClassKind matchTokenString(StringRef Name) {
  return InvalidMatchClass;
}

/// isSubclass - Compute whether \p A is a subclass of \p B.
static bool isSubclass(MatchClassKind A, MatchClassKind B) {
  if (A == B)
    return true;

  switch (A) {
  default:
    return false;

  case MCK_R600_TReg32_X:
    switch (B) {
    default: return false;
    case MCK_R600_TReg32: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_TReg32_Y:
    switch (B) {
    default: return false;
    case MCK_R600_TReg32: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_TReg32_Z:
    switch (B) {
    default: return false;
    case MCK_R600_TReg32: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_TReg32_W:
    switch (B) {
    default: return false;
    case MCK_R600_TReg32: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_TReg32:
    return B == MCK_R600_Reg32;

  case MCK_R600_Addr:
    return B == MCK_R600_Reg32;

  case MCK_R600_KC1_X:
    switch (B) {
    default: return false;
    case MCK_R600_KC1: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_KC1_Y:
    switch (B) {
    default: return false;
    case MCK_R600_KC1: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_KC1_Z:
    switch (B) {
    default: return false;
    case MCK_R600_KC1: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_KC1_W:
    switch (B) {
    default: return false;
    case MCK_R600_KC1: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_R600_KC1:
    return B == MCK_R600_Reg32;

  case MCK_R600_ArrayBase:
    return B == MCK_R600_Reg32;

  case MCK_Reg34:
    switch (B) {
    default: return false;
    case MCK_R600_LDS_SRC_REG: return true;
    case MCK_R600_Reg32: return true;
    }

  case MCK_Reg12:
    return B == MCK_R600_Reg128Vertical;

  case MCK_Reg14:
    return B == MCK_R600_Reg128Vertical;

  case MCK_Reg15:
    return B == MCK_R600_Reg128Vertical;

  case MCK_Reg16:
    return B == MCK_R600_Reg128Vertical;

  case MCK_Reg18:
    return B == MCK_R600_Reg64Vertical;

  case MCK_Reg19:
    return B == MCK_R600_Reg64Vertical;

  case MCK_Reg20:
    return B == MCK_R600_Reg64Vertical;

  case MCK_Reg21:
    return B == MCK_R600_Reg64Vertical;

  case MCK_R600_KC0_X:
    switch (B) {
    default: return false;
    case MCK_R600_Reg32: return true;
    case MCK_R600_KC0: return true;
    }

  case MCK_R600_KC0_Y:
    switch (B) {
    default: return false;
    case MCK_R600_Reg32: return true;
    case MCK_R600_KC0: return true;
    }

  case MCK_R600_KC0_Z:
    switch (B) {
    default: return false;
    case MCK_R600_Reg32: return true;
    case MCK_R600_KC0: return true;
    }

  case MCK_R600_KC0_W:
    switch (B) {
    default: return false;
    case MCK_R600_Reg32: return true;
    case MCK_R600_KC0: return true;
    }

  case MCK_R600_KC0:
    return B == MCK_R600_Reg32;

  case MCK_SReg_32:
    return B == MCK_VS_32;

  case MCK_VCCReg:
    switch (B) {
    default: return false;
    case MCK_SReg_64: return true;
    case MCK_VS_64: return true;
    }

  case MCK_EXECReg:
    switch (B) {
    default: return false;
    case MCK_SReg_64: return true;
    case MCK_VS_64: return true;
    }

  case MCK_SReg_64:
    return B == MCK_VS_64;

  case MCK_M0Reg:
    switch (B) {
    default: return false;
    case MCK_SReg_32: return true;
    case MCK_VS_32: return true;
    }

  case MCK_SGPR_32:
    switch (B) {
    default: return false;
    case MCK_SReg_32: return true;
    case MCK_VS_32: return true;
    }

  case MCK_VReg_1:
    return B == MCK_VS_32;

  case MCK_SReg_128:
    return B == MCK_VSrc_128;

  case MCK_SGPR_64:
    switch (B) {
    default: return false;
    case MCK_SReg_64: return true;
    case MCK_VS_64: return true;
    }

  case MCK_VReg_128:
    return B == MCK_VSrc_128;

  case MCK_VReg_64:
    return B == MCK_VS_64;
  }
}

static unsigned validateOperandClass(MCParsedAsmOperand &GOp, MatchClassKind Kind) {
  AMDGPUOperand &Operand = (AMDGPUOperand&)GOp;
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

  // 'SWaitCnt' class
  if (Kind == MCK_SWaitCnt) {
    if (Operand.isSWaitCnt())
      return MCTargetAsmParser::Match_Success;
  }

  if (Operand.isReg()) {
    MatchClassKind OpKind;
    switch (Operand.getReg()) {
    default: OpKind = InvalidMatchClass; break;
    case AMDGPU::T0_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T0_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T0_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T0_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T1_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T1_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T1_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T1_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T2_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T2_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T2_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T2_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T3_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T3_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T3_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T3_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T4_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T4_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T4_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T4_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T5_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T5_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T5_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T5_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T6_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T6_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T6_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T6_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T7_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T7_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T7_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T7_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T8_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T8_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T8_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T8_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T9_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T9_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T9_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T9_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T10_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T10_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T10_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T10_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T11_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T11_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T11_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T11_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T12_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T12_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T12_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T12_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T13_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T13_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T13_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T13_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T14_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T14_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T14_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T14_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T15_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T15_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T15_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T15_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T16_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T16_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T16_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T16_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T17_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T17_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T17_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T17_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T18_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T18_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T18_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T18_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T19_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T19_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T19_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T19_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T20_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T20_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T20_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T20_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T21_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T21_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T21_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T21_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T22_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T22_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T22_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T22_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T23_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T23_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T23_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T23_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T24_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T24_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T24_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T24_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T25_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T25_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T25_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T25_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T26_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T26_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T26_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T26_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T27_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T27_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T27_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T27_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T28_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T28_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T28_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T28_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T29_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T29_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T29_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T29_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T30_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T30_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T30_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T30_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T31_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T31_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T31_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T31_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T32_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T32_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T32_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T32_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T33_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T33_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T33_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T33_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T34_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T34_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T34_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T34_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T35_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T35_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T35_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T35_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T36_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T36_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T36_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T36_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T37_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T37_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T37_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T37_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T38_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T38_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T38_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T38_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T39_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T39_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T39_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T39_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T40_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T40_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T40_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T40_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T41_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T41_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T41_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T41_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T42_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T42_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T42_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T42_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T43_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T43_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T43_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T43_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T44_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T44_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T44_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T44_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T45_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T45_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T45_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T45_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T46_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T46_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T46_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T46_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T47_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T47_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T47_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T47_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T48_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T48_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T48_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T48_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T49_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T49_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T49_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T49_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T50_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T50_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T50_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T50_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T51_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T51_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T51_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T51_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T52_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T52_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T52_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T52_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T53_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T53_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T53_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T53_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T54_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T54_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T54_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T54_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T55_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T55_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T55_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T55_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T56_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T56_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T56_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T56_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T57_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T57_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T57_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T57_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T58_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T58_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T58_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T58_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T59_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T59_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T59_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T59_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T60_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T60_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T60_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T60_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T61_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T61_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T61_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T61_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T62_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T62_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T62_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T62_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T63_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T63_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T63_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T63_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T64_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T64_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T64_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T64_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T65_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T65_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T65_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T65_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T66_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T66_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T66_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T66_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T67_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T67_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T67_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T67_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T68_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T68_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T68_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T68_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T69_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T69_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T69_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T69_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T70_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T70_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T70_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T70_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T71_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T71_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T71_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T71_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T72_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T72_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T72_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T72_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T73_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T73_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T73_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T73_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T74_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T74_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T74_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T74_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T75_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T75_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T75_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T75_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T76_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T76_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T76_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T76_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T77_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T77_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T77_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T77_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T78_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T78_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T78_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T78_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T79_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T79_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T79_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T79_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T80_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T80_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T80_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T80_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T81_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T81_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T81_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T81_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T82_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T82_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T82_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T82_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T83_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T83_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T83_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T83_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T84_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T84_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T84_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T84_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T85_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T85_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T85_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T85_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T86_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T86_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T86_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T86_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T87_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T87_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T87_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T87_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T88_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T88_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T88_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T88_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T89_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T89_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T89_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T89_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T90_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T90_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T90_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T90_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T91_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T91_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T91_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T91_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T92_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T92_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T92_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T92_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T93_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T93_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T93_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T93_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T94_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T94_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T94_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T94_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T95_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T95_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T95_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T95_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T96_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T96_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T96_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T96_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T97_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T97_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T97_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T97_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T98_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T98_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T98_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T98_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T99_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T99_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T99_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T99_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T100_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T100_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T100_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T100_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T101_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T101_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T101_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T101_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T102_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T102_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T102_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T102_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T103_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T103_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T103_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T103_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T104_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T104_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T104_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T104_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T105_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T105_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T105_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T105_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T106_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T106_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T106_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T106_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T107_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T107_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T107_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T107_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T108_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T108_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T108_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T108_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T109_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T109_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T109_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T109_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T110_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T110_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T110_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T110_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T111_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T111_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T111_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T111_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T112_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T112_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T112_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T112_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T113_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T113_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T113_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T113_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T114_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T114_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T114_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T114_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T115_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T115_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T115_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T115_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T116_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T116_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T116_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T116_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T117_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T117_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T117_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T117_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T118_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T118_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T118_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T118_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T119_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T119_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T119_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T119_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T120_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T120_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T120_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T120_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T121_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T121_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T121_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T121_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T122_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T122_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T122_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T122_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T123_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T123_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T123_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T123_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T124_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T124_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T124_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T124_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T125_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T125_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T125_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T125_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T126_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T126_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T126_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T126_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::T127_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::T127_Y: OpKind = MCK_R600_TReg32_Y; break;
    case AMDGPU::T127_Z: OpKind = MCK_R600_TReg32_Z; break;
    case AMDGPU::T127_W: OpKind = MCK_R600_TReg32_W; break;
    case AMDGPU::Addr0_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr0_Y: OpKind = MCK_R600_Addr_Y; break;
    case AMDGPU::Addr0_Z: OpKind = MCK_R600_Addr_Z; break;
    case AMDGPU::Addr0_W: OpKind = MCK_R600_Addr_W; break;
    case AMDGPU::Addr1_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr2_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr3_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr4_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr5_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr6_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr7_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr8_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr9_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr10_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr11_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr12_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr13_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr14_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr15_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr16_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr17_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr18_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr19_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr20_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr21_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr22_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr23_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr24_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr25_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr26_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr27_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr28_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr29_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr30_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr31_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr32_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr33_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr34_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr35_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr36_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr37_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr38_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr39_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr40_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr41_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr42_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr43_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr44_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr45_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr46_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr47_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr48_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr49_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr50_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr51_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr52_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr53_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr54_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr55_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr56_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr57_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr58_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr59_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr60_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr61_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr62_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr63_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr64_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr65_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr66_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr67_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr68_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr69_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr70_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr71_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr72_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr73_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr74_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr75_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr76_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr77_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr78_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr79_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr80_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr81_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr82_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr83_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr84_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr85_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr86_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr87_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr88_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr89_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr90_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr91_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr92_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr93_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr94_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr95_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr96_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr97_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr98_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr99_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr100_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr101_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr102_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr103_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr104_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr105_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr106_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr107_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr108_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr109_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr110_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr111_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr112_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr113_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr114_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr115_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr116_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr117_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr118_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr119_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr120_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr121_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr122_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr123_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr124_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr125_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr126_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::Addr127_X: OpKind = MCK_R600_Addr; break;
    case AMDGPU::T0_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T1_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T2_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T3_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T4_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T5_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T6_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T7_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T8_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T9_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T10_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T11_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T12_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T13_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T14_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T15_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T16_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T17_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T18_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T19_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T20_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T21_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T22_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T23_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T24_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T25_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T26_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T27_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T28_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T29_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T30_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T31_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T32_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T33_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T34_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T35_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T36_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T37_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T38_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T39_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T40_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T41_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T42_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T43_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T44_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T45_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T46_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T47_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T48_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T49_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T50_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T51_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T52_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T53_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T54_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T55_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T56_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T57_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T58_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T59_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T60_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T61_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T62_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T63_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T64_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T65_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T66_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T67_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T68_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T69_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T70_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T71_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T72_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T73_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T74_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T75_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T76_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T77_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T78_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T79_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T80_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T81_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T82_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T83_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T84_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T85_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T86_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T87_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T88_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T89_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T90_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T91_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T92_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T93_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T94_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T95_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T96_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T97_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T98_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T99_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T100_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T101_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T102_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T103_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T104_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T105_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T106_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T107_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T108_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T109_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T110_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T111_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T112_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T113_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T114_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T115_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T116_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T117_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T118_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T119_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T120_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T121_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T122_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T123_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T124_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T125_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T126_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T127_XYZW: OpKind = MCK_R600_Reg128; break;
    case AMDGPU::T0_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T1_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T2_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T3_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T4_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T5_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T6_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T7_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T8_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T9_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T10_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T11_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T12_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T13_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T14_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T15_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T16_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T17_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T18_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T19_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T20_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T21_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T22_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T23_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T24_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T25_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T26_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T27_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T28_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T29_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T30_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T31_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T32_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T33_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T34_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T35_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T36_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T37_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T38_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T39_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T40_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T41_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T42_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T43_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T44_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T45_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T46_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T47_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T48_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T49_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T50_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T51_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T52_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T53_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T54_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T55_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T56_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T57_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T58_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T59_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T60_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T61_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T62_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::T63_XY: OpKind = MCK_R600_Reg64; break;
    case AMDGPU::V0123_X: OpKind = MCK_Reg12; break;
    case AMDGPU::V0123_Y: OpKind = MCK_Reg14; break;
    case AMDGPU::V0123_Z: OpKind = MCK_Reg15; break;
    case AMDGPU::V0123_W: OpKind = MCK_Reg16; break;
    case AMDGPU::V01_X: OpKind = MCK_Reg18; break;
    case AMDGPU::V01_Y: OpKind = MCK_Reg19; break;
    case AMDGPU::V01_Z: OpKind = MCK_Reg20; break;
    case AMDGPU::V01_W: OpKind = MCK_Reg21; break;
    case AMDGPU::V23_X: OpKind = MCK_Reg18; break;
    case AMDGPU::V23_Y: OpKind = MCK_Reg19; break;
    case AMDGPU::V23_Z: OpKind = MCK_Reg20; break;
    case AMDGPU::V23_W: OpKind = MCK_Reg21; break;
    case AMDGPU::KC0_159_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_159_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_159_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_159_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_158_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_158_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_158_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_158_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_157_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_157_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_157_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_157_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_156_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_156_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_156_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_156_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_155_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_155_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_155_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_155_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_154_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_154_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_154_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_154_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_153_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_153_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_153_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_153_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_152_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_152_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_152_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_152_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_151_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_151_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_151_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_151_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_150_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_150_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_150_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_150_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_149_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_149_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_149_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_149_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_148_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_148_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_148_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_148_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_147_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_147_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_147_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_147_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_146_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_146_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_146_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_146_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_145_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_145_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_145_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_145_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_144_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_144_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_144_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_144_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_143_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_143_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_143_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_143_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_142_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_142_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_142_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_142_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_141_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_141_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_141_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_141_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_140_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_140_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_140_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_140_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_139_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_139_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_139_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_139_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_138_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_138_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_138_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_138_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_137_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_137_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_137_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_137_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_136_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_136_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_136_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_136_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_135_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_135_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_135_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_135_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_134_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_134_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_134_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_134_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_133_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_133_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_133_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_133_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_132_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_132_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_132_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_132_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_131_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_131_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_131_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_131_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_130_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_130_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_130_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_130_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_129_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_129_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_129_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_129_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC0_128_X: OpKind = MCK_R600_KC0_X; break;
    case AMDGPU::KC0_128_Y: OpKind = MCK_R600_KC0_Y; break;
    case AMDGPU::KC0_128_Z: OpKind = MCK_R600_KC0_Z; break;
    case AMDGPU::KC0_128_W: OpKind = MCK_R600_KC0_W; break;
    case AMDGPU::KC1_191_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_191_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_191_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_191_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_190_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_190_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_190_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_190_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_189_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_189_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_189_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_189_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_188_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_188_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_188_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_188_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_187_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_187_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_187_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_187_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_186_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_186_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_186_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_186_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_185_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_185_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_185_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_185_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_184_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_184_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_184_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_184_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_183_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_183_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_183_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_183_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_182_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_182_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_182_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_182_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_181_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_181_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_181_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_181_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_180_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_180_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_180_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_180_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_179_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_179_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_179_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_179_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_178_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_178_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_178_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_178_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_177_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_177_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_177_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_177_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_176_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_176_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_176_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_176_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_175_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_175_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_175_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_175_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_174_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_174_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_174_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_174_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_173_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_173_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_173_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_173_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_172_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_172_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_172_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_172_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_171_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_171_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_171_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_171_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_170_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_170_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_170_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_170_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_169_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_169_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_169_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_169_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_168_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_168_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_168_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_168_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_167_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_167_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_167_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_167_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_166_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_166_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_166_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_166_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_165_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_165_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_165_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_165_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_164_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_164_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_164_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_164_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_163_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_163_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_163_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_163_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_162_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_162_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_162_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_162_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_161_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_161_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_161_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_161_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::KC1_160_X: OpKind = MCK_R600_KC1_X; break;
    case AMDGPU::KC1_160_Y: OpKind = MCK_R600_KC1_Y; break;
    case AMDGPU::KC1_160_Z: OpKind = MCK_R600_KC1_Z; break;
    case AMDGPU::KC1_160_W: OpKind = MCK_R600_KC1_W; break;
    case AMDGPU::ArrayBase448: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase449: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase450: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase451: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase452: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase453: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase454: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase455: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase456: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase457: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase458: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase459: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase460: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase461: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase462: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase463: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase464: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase465: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase466: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase467: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase468: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase469: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase470: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase471: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase472: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase473: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase474: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase475: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase476: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase477: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase478: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase479: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::ArrayBase480: OpKind = MCK_R600_ArrayBase; break;
    case AMDGPU::OQA: OpKind = MCK_R600_LDS_SRC_REG; break;
    case AMDGPU::OQB: OpKind = MCK_R600_LDS_SRC_REG; break;
    case AMDGPU::OQAP: OpKind = MCK_Reg34; break;
    case AMDGPU::OQBP: OpKind = MCK_R600_LDS_SRC_REG; break;
    case AMDGPU::LDS_DIRECT_A: OpKind = MCK_R600_LDS_SRC_REG; break;
    case AMDGPU::LDS_DIRECT_B: OpKind = MCK_R600_LDS_SRC_REG; break;
    case AMDGPU::ZERO: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::ONE: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::NEG_ONE: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::ONE_INT: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::HALF: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::NEG_HALF: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::ALU_LITERAL_X: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::PV_X: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::PREDICATE_BIT: OpKind = MCK_R600_Predicate_Bit; break;
    case AMDGPU::PRED_SEL_OFF: OpKind = MCK_R600_Predicate; break;
    case AMDGPU::PRED_SEL_ZERO: OpKind = MCK_R600_Predicate; break;
    case AMDGPU::PRED_SEL_ONE: OpKind = MCK_R600_Predicate; break;
    case AMDGPU::AR_X: OpKind = MCK_R600_TReg32_X; break;
    case AMDGPU::ALU_CONST: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::ALU_PARAM: OpKind = MCK_R600_Reg32; break;
    case AMDGPU::VCC_LO: OpKind = MCK_SReg_32; break;
    case AMDGPU::VCC_HI: OpKind = MCK_SReg_32; break;
    case AMDGPU::VCC: OpKind = MCK_VCCReg; break;
    case AMDGPU::EXEC_LO: OpKind = MCK_SReg_32; break;
    case AMDGPU::EXEC_HI: OpKind = MCK_SReg_32; break;
    case AMDGPU::EXEC: OpKind = MCK_EXECReg; break;
    case AMDGPU::SCC: OpKind = MCK_SCCReg; break;
    case AMDGPU::M0: OpKind = MCK_M0Reg; break;
    case AMDGPU::FLAT_SCR_LO: OpKind = MCK_SReg_32; break;
    case AMDGPU::FLAT_SCR_HI: OpKind = MCK_SReg_32; break;
    case AMDGPU::FLAT_SCR: OpKind = MCK_SReg_64; break;
    case AMDGPU::SGPR0: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR1: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR2: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR3: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR4: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR5: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR6: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR7: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR8: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR9: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR10: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR11: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR12: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR13: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR14: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR15: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR16: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR17: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR18: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR19: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR20: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR21: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR22: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR23: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR24: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR25: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR26: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR27: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR28: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR29: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR30: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR31: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR32: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR33: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR34: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR35: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR36: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR37: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR38: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR39: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR40: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR41: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR42: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR43: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR44: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR45: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR46: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR47: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR48: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR49: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR50: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR51: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR52: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR53: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR54: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR55: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR56: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR57: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR58: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR59: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR60: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR61: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR62: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR63: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR64: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR65: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR66: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR67: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR68: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR69: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR70: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR71: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR72: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR73: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR74: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR75: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR76: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR77: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR78: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR79: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR80: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR81: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR82: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR83: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR84: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR85: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR86: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR87: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR88: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR89: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR90: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR91: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR92: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR93: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR94: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR95: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR96: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR97: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR98: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR99: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR100: OpKind = MCK_SGPR_32; break;
    case AMDGPU::SGPR101: OpKind = MCK_SGPR_32; break;
    case AMDGPU::VGPR0: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR1: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR2: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR3: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR4: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR5: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR6: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR7: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR8: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR9: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR10: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR11: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR12: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR13: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR14: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR15: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR16: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR17: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR18: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR19: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR20: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR21: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR22: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR23: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR24: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR25: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR26: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR27: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR28: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR29: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR30: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR31: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR32: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR33: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR34: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR35: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR36: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR37: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR38: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR39: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR40: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR41: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR42: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR43: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR44: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR45: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR46: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR47: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR48: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR49: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR50: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR51: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR52: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR53: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR54: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR55: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR56: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR57: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR58: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR59: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR60: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR61: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR62: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR63: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR64: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR65: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR66: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR67: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR68: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR69: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR70: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR71: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR72: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR73: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR74: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR75: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR76: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR77: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR78: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR79: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR80: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR81: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR82: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR83: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR84: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR85: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR86: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR87: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR88: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR89: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR90: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR91: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR92: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR93: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR94: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR95: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR96: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR97: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR98: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR99: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR100: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR101: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR102: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR103: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR104: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR105: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR106: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR107: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR108: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR109: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR110: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR111: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR112: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR113: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR114: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR115: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR116: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR117: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR118: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR119: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR120: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR121: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR122: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR123: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR124: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR125: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR126: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR127: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR128: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR129: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR130: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR131: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR132: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR133: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR134: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR135: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR136: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR137: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR138: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR139: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR140: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR141: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR142: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR143: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR144: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR145: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR146: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR147: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR148: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR149: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR150: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR151: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR152: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR153: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR154: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR155: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR156: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR157: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR158: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR159: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR160: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR161: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR162: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR163: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR164: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR165: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR166: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR167: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR168: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR169: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR170: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR171: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR172: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR173: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR174: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR175: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR176: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR177: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR178: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR179: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR180: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR181: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR182: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR183: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR184: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR185: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR186: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR187: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR188: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR189: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR190: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR191: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR192: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR193: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR194: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR195: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR196: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR197: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR198: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR199: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR200: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR201: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR202: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR203: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR204: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR205: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR206: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR207: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR208: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR209: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR210: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR211: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR212: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR213: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR214: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR215: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR216: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR217: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR218: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR219: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR220: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR221: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR222: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR223: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR224: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR225: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR226: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR227: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR228: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR229: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR230: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR231: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR232: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR233: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR234: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR235: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR236: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR237: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR238: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR239: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR240: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR241: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR242: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR243: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR244: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR245: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR246: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR247: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR248: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR249: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR250: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR251: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR252: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR253: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR254: OpKind = MCK_VReg_1; break;
    case AMDGPU::VGPR255: OpKind = MCK_VReg_1; break;
    case AMDGPU::SGPR0_SGPR1_SGPR2_SGPR3: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR4_SGPR5_SGPR6_SGPR7: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR8_SGPR9_SGPR10_SGPR11: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR12_SGPR13_SGPR14_SGPR15: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR16_SGPR17_SGPR18_SGPR19: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR20_SGPR21_SGPR22_SGPR23: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR24_SGPR25_SGPR26_SGPR27: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR28_SGPR29_SGPR30_SGPR31: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR32_SGPR33_SGPR34_SGPR35: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR36_SGPR37_SGPR38_SGPR39: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR40_SGPR41_SGPR42_SGPR43: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR44_SGPR45_SGPR46_SGPR47: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR48_SGPR49_SGPR50_SGPR51: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR52_SGPR53_SGPR54_SGPR55: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR56_SGPR57_SGPR58_SGPR59: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR60_SGPR61_SGPR62_SGPR63: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR64_SGPR65_SGPR66_SGPR67: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR68_SGPR69_SGPR70_SGPR71: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR72_SGPR73_SGPR74_SGPR75: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR76_SGPR77_SGPR78_SGPR79: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR80_SGPR81_SGPR82_SGPR83: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR84_SGPR85_SGPR86_SGPR87: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR88_SGPR89_SGPR90_SGPR91: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR92_SGPR93_SGPR94_SGPR95: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR96_SGPR97_SGPR98_SGPR99: OpKind = MCK_SReg_128; break;
    case AMDGPU::SGPR0_SGPR1_SGPR2_SGPR3_SGPR4_SGPR5_SGPR6_SGPR7: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR4_SGPR5_SGPR6_SGPR7_SGPR8_SGPR9_SGPR10_SGPR11: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR8_SGPR9_SGPR10_SGPR11_SGPR12_SGPR13_SGPR14_SGPR15: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR12_SGPR13_SGPR14_SGPR15_SGPR16_SGPR17_SGPR18_SGPR19: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR16_SGPR17_SGPR18_SGPR19_SGPR20_SGPR21_SGPR22_SGPR23: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR20_SGPR21_SGPR22_SGPR23_SGPR24_SGPR25_SGPR26_SGPR27: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR24_SGPR25_SGPR26_SGPR27_SGPR28_SGPR29_SGPR30_SGPR31: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR28_SGPR29_SGPR30_SGPR31_SGPR32_SGPR33_SGPR34_SGPR35: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR32_SGPR33_SGPR34_SGPR35_SGPR36_SGPR37_SGPR38_SGPR39: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR36_SGPR37_SGPR38_SGPR39_SGPR40_SGPR41_SGPR42_SGPR43: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR40_SGPR41_SGPR42_SGPR43_SGPR44_SGPR45_SGPR46_SGPR47: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR44_SGPR45_SGPR46_SGPR47_SGPR48_SGPR49_SGPR50_SGPR51: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR48_SGPR49_SGPR50_SGPR51_SGPR52_SGPR53_SGPR54_SGPR55: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR52_SGPR53_SGPR54_SGPR55_SGPR56_SGPR57_SGPR58_SGPR59: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR56_SGPR57_SGPR58_SGPR59_SGPR60_SGPR61_SGPR62_SGPR63: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR60_SGPR61_SGPR62_SGPR63_SGPR64_SGPR65_SGPR66_SGPR67: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR64_SGPR65_SGPR66_SGPR67_SGPR68_SGPR69_SGPR70_SGPR71: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR68_SGPR69_SGPR70_SGPR71_SGPR72_SGPR73_SGPR74_SGPR75: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR72_SGPR73_SGPR74_SGPR75_SGPR76_SGPR77_SGPR78_SGPR79: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR76_SGPR77_SGPR78_SGPR79_SGPR80_SGPR81_SGPR82_SGPR83: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR80_SGPR81_SGPR82_SGPR83_SGPR84_SGPR85_SGPR86_SGPR87: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR84_SGPR85_SGPR86_SGPR87_SGPR88_SGPR89_SGPR90_SGPR91: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR88_SGPR89_SGPR90_SGPR91_SGPR92_SGPR93_SGPR94_SGPR95: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR92_SGPR93_SGPR94_SGPR95_SGPR96_SGPR97_SGPR98_SGPR99: OpKind = MCK_SReg_256; break;
    case AMDGPU::SGPR0_SGPR1_SGPR2_SGPR3_SGPR4_SGPR5_SGPR6_SGPR7_SGPR8_SGPR9_SGPR10_SGPR11_SGPR12_SGPR13_SGPR14_SGPR15: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR4_SGPR5_SGPR6_SGPR7_SGPR8_SGPR9_SGPR10_SGPR11_SGPR12_SGPR13_SGPR14_SGPR15_SGPR16_SGPR17_SGPR18_SGPR19: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR8_SGPR9_SGPR10_SGPR11_SGPR12_SGPR13_SGPR14_SGPR15_SGPR16_SGPR17_SGPR18_SGPR19_SGPR20_SGPR21_SGPR22_SGPR23: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR12_SGPR13_SGPR14_SGPR15_SGPR16_SGPR17_SGPR18_SGPR19_SGPR20_SGPR21_SGPR22_SGPR23_SGPR24_SGPR25_SGPR26_SGPR27: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR16_SGPR17_SGPR18_SGPR19_SGPR20_SGPR21_SGPR22_SGPR23_SGPR24_SGPR25_SGPR26_SGPR27_SGPR28_SGPR29_SGPR30_SGPR31: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR20_SGPR21_SGPR22_SGPR23_SGPR24_SGPR25_SGPR26_SGPR27_SGPR28_SGPR29_SGPR30_SGPR31_SGPR32_SGPR33_SGPR34_SGPR35: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR24_SGPR25_SGPR26_SGPR27_SGPR28_SGPR29_SGPR30_SGPR31_SGPR32_SGPR33_SGPR34_SGPR35_SGPR36_SGPR37_SGPR38_SGPR39: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR28_SGPR29_SGPR30_SGPR31_SGPR32_SGPR33_SGPR34_SGPR35_SGPR36_SGPR37_SGPR38_SGPR39_SGPR40_SGPR41_SGPR42_SGPR43: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR32_SGPR33_SGPR34_SGPR35_SGPR36_SGPR37_SGPR38_SGPR39_SGPR40_SGPR41_SGPR42_SGPR43_SGPR44_SGPR45_SGPR46_SGPR47: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR36_SGPR37_SGPR38_SGPR39_SGPR40_SGPR41_SGPR42_SGPR43_SGPR44_SGPR45_SGPR46_SGPR47_SGPR48_SGPR49_SGPR50_SGPR51: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR40_SGPR41_SGPR42_SGPR43_SGPR44_SGPR45_SGPR46_SGPR47_SGPR48_SGPR49_SGPR50_SGPR51_SGPR52_SGPR53_SGPR54_SGPR55: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR44_SGPR45_SGPR46_SGPR47_SGPR48_SGPR49_SGPR50_SGPR51_SGPR52_SGPR53_SGPR54_SGPR55_SGPR56_SGPR57_SGPR58_SGPR59: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR48_SGPR49_SGPR50_SGPR51_SGPR52_SGPR53_SGPR54_SGPR55_SGPR56_SGPR57_SGPR58_SGPR59_SGPR60_SGPR61_SGPR62_SGPR63: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR52_SGPR53_SGPR54_SGPR55_SGPR56_SGPR57_SGPR58_SGPR59_SGPR60_SGPR61_SGPR62_SGPR63_SGPR64_SGPR65_SGPR66_SGPR67: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR56_SGPR57_SGPR58_SGPR59_SGPR60_SGPR61_SGPR62_SGPR63_SGPR64_SGPR65_SGPR66_SGPR67_SGPR68_SGPR69_SGPR70_SGPR71: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR60_SGPR61_SGPR62_SGPR63_SGPR64_SGPR65_SGPR66_SGPR67_SGPR68_SGPR69_SGPR70_SGPR71_SGPR72_SGPR73_SGPR74_SGPR75: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR64_SGPR65_SGPR66_SGPR67_SGPR68_SGPR69_SGPR70_SGPR71_SGPR72_SGPR73_SGPR74_SGPR75_SGPR76_SGPR77_SGPR78_SGPR79: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR68_SGPR69_SGPR70_SGPR71_SGPR72_SGPR73_SGPR74_SGPR75_SGPR76_SGPR77_SGPR78_SGPR79_SGPR80_SGPR81_SGPR82_SGPR83: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR72_SGPR73_SGPR74_SGPR75_SGPR76_SGPR77_SGPR78_SGPR79_SGPR80_SGPR81_SGPR82_SGPR83_SGPR84_SGPR85_SGPR86_SGPR87: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR76_SGPR77_SGPR78_SGPR79_SGPR80_SGPR81_SGPR82_SGPR83_SGPR84_SGPR85_SGPR86_SGPR87_SGPR88_SGPR89_SGPR90_SGPR91: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR80_SGPR81_SGPR82_SGPR83_SGPR84_SGPR85_SGPR86_SGPR87_SGPR88_SGPR89_SGPR90_SGPR91_SGPR92_SGPR93_SGPR94_SGPR95: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR84_SGPR85_SGPR86_SGPR87_SGPR88_SGPR89_SGPR90_SGPR91_SGPR92_SGPR93_SGPR94_SGPR95_SGPR96_SGPR97_SGPR98_SGPR99: OpKind = MCK_SReg_512; break;
    case AMDGPU::SGPR0_SGPR1: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR2_SGPR3: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR4_SGPR5: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR6_SGPR7: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR8_SGPR9: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR10_SGPR11: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR12_SGPR13: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR14_SGPR15: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR16_SGPR17: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR18_SGPR19: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR20_SGPR21: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR22_SGPR23: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR24_SGPR25: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR26_SGPR27: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR28_SGPR29: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR30_SGPR31: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR32_SGPR33: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR34_SGPR35: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR36_SGPR37: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR38_SGPR39: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR40_SGPR41: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR42_SGPR43: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR44_SGPR45: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR46_SGPR47: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR48_SGPR49: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR50_SGPR51: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR52_SGPR53: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR54_SGPR55: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR56_SGPR57: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR58_SGPR59: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR60_SGPR61: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR62_SGPR63: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR64_SGPR65: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR66_SGPR67: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR68_SGPR69: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR70_SGPR71: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR72_SGPR73: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR74_SGPR75: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR76_SGPR77: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR78_SGPR79: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR80_SGPR81: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR82_SGPR83: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR84_SGPR85: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR86_SGPR87: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR88_SGPR89: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR90_SGPR91: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR92_SGPR93: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR94_SGPR95: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR96_SGPR97: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR98_SGPR99: OpKind = MCK_SGPR_64; break;
    case AMDGPU::SGPR100_SGPR101: OpKind = MCK_SGPR_64; break;
    case AMDGPU::VGPR0_VGPR1_VGPR2_VGPR3: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR1_VGPR2_VGPR3_VGPR4: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR2_VGPR3_VGPR4_VGPR5: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR3_VGPR4_VGPR5_VGPR6: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR4_VGPR5_VGPR6_VGPR7: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR5_VGPR6_VGPR7_VGPR8: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR6_VGPR7_VGPR8_VGPR9: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR7_VGPR8_VGPR9_VGPR10: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR8_VGPR9_VGPR10_VGPR11: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR9_VGPR10_VGPR11_VGPR12: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR10_VGPR11_VGPR12_VGPR13: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR11_VGPR12_VGPR13_VGPR14: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR12_VGPR13_VGPR14_VGPR15: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR13_VGPR14_VGPR15_VGPR16: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR14_VGPR15_VGPR16_VGPR17: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR15_VGPR16_VGPR17_VGPR18: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR16_VGPR17_VGPR18_VGPR19: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR17_VGPR18_VGPR19_VGPR20: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR18_VGPR19_VGPR20_VGPR21: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR19_VGPR20_VGPR21_VGPR22: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR20_VGPR21_VGPR22_VGPR23: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR21_VGPR22_VGPR23_VGPR24: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR22_VGPR23_VGPR24_VGPR25: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR23_VGPR24_VGPR25_VGPR26: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR24_VGPR25_VGPR26_VGPR27: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR25_VGPR26_VGPR27_VGPR28: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR26_VGPR27_VGPR28_VGPR29: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR27_VGPR28_VGPR29_VGPR30: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR28_VGPR29_VGPR30_VGPR31: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR29_VGPR30_VGPR31_VGPR32: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR30_VGPR31_VGPR32_VGPR33: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR31_VGPR32_VGPR33_VGPR34: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR32_VGPR33_VGPR34_VGPR35: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR33_VGPR34_VGPR35_VGPR36: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR34_VGPR35_VGPR36_VGPR37: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR35_VGPR36_VGPR37_VGPR38: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR36_VGPR37_VGPR38_VGPR39: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR37_VGPR38_VGPR39_VGPR40: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR38_VGPR39_VGPR40_VGPR41: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR39_VGPR40_VGPR41_VGPR42: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR40_VGPR41_VGPR42_VGPR43: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR41_VGPR42_VGPR43_VGPR44: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR42_VGPR43_VGPR44_VGPR45: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR43_VGPR44_VGPR45_VGPR46: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR44_VGPR45_VGPR46_VGPR47: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR45_VGPR46_VGPR47_VGPR48: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR46_VGPR47_VGPR48_VGPR49: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR47_VGPR48_VGPR49_VGPR50: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR48_VGPR49_VGPR50_VGPR51: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR49_VGPR50_VGPR51_VGPR52: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR50_VGPR51_VGPR52_VGPR53: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR51_VGPR52_VGPR53_VGPR54: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR52_VGPR53_VGPR54_VGPR55: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR53_VGPR54_VGPR55_VGPR56: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR54_VGPR55_VGPR56_VGPR57: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR55_VGPR56_VGPR57_VGPR58: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR56_VGPR57_VGPR58_VGPR59: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR57_VGPR58_VGPR59_VGPR60: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR58_VGPR59_VGPR60_VGPR61: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR59_VGPR60_VGPR61_VGPR62: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR60_VGPR61_VGPR62_VGPR63: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR61_VGPR62_VGPR63_VGPR64: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR62_VGPR63_VGPR64_VGPR65: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR63_VGPR64_VGPR65_VGPR66: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR64_VGPR65_VGPR66_VGPR67: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR65_VGPR66_VGPR67_VGPR68: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR66_VGPR67_VGPR68_VGPR69: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR67_VGPR68_VGPR69_VGPR70: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR68_VGPR69_VGPR70_VGPR71: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR69_VGPR70_VGPR71_VGPR72: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR70_VGPR71_VGPR72_VGPR73: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR71_VGPR72_VGPR73_VGPR74: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR72_VGPR73_VGPR74_VGPR75: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR73_VGPR74_VGPR75_VGPR76: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR74_VGPR75_VGPR76_VGPR77: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR75_VGPR76_VGPR77_VGPR78: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR76_VGPR77_VGPR78_VGPR79: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR77_VGPR78_VGPR79_VGPR80: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR78_VGPR79_VGPR80_VGPR81: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR79_VGPR80_VGPR81_VGPR82: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR80_VGPR81_VGPR82_VGPR83: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR81_VGPR82_VGPR83_VGPR84: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR82_VGPR83_VGPR84_VGPR85: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR83_VGPR84_VGPR85_VGPR86: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR84_VGPR85_VGPR86_VGPR87: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR85_VGPR86_VGPR87_VGPR88: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR86_VGPR87_VGPR88_VGPR89: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR87_VGPR88_VGPR89_VGPR90: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR88_VGPR89_VGPR90_VGPR91: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR89_VGPR90_VGPR91_VGPR92: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR90_VGPR91_VGPR92_VGPR93: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR91_VGPR92_VGPR93_VGPR94: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR92_VGPR93_VGPR94_VGPR95: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR93_VGPR94_VGPR95_VGPR96: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR94_VGPR95_VGPR96_VGPR97: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR95_VGPR96_VGPR97_VGPR98: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR96_VGPR97_VGPR98_VGPR99: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR97_VGPR98_VGPR99_VGPR100: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR98_VGPR99_VGPR100_VGPR101: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR99_VGPR100_VGPR101_VGPR102: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR100_VGPR101_VGPR102_VGPR103: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR101_VGPR102_VGPR103_VGPR104: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR102_VGPR103_VGPR104_VGPR105: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR103_VGPR104_VGPR105_VGPR106: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR104_VGPR105_VGPR106_VGPR107: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR105_VGPR106_VGPR107_VGPR108: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR106_VGPR107_VGPR108_VGPR109: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR107_VGPR108_VGPR109_VGPR110: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR108_VGPR109_VGPR110_VGPR111: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR109_VGPR110_VGPR111_VGPR112: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR110_VGPR111_VGPR112_VGPR113: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR111_VGPR112_VGPR113_VGPR114: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR112_VGPR113_VGPR114_VGPR115: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR113_VGPR114_VGPR115_VGPR116: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR114_VGPR115_VGPR116_VGPR117: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR115_VGPR116_VGPR117_VGPR118: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR116_VGPR117_VGPR118_VGPR119: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR117_VGPR118_VGPR119_VGPR120: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR118_VGPR119_VGPR120_VGPR121: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR119_VGPR120_VGPR121_VGPR122: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR120_VGPR121_VGPR122_VGPR123: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR121_VGPR122_VGPR123_VGPR124: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR122_VGPR123_VGPR124_VGPR125: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR123_VGPR124_VGPR125_VGPR126: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR124_VGPR125_VGPR126_VGPR127: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR125_VGPR126_VGPR127_VGPR128: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR126_VGPR127_VGPR128_VGPR129: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR127_VGPR128_VGPR129_VGPR130: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR128_VGPR129_VGPR130_VGPR131: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR129_VGPR130_VGPR131_VGPR132: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR130_VGPR131_VGPR132_VGPR133: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR131_VGPR132_VGPR133_VGPR134: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR132_VGPR133_VGPR134_VGPR135: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR133_VGPR134_VGPR135_VGPR136: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR134_VGPR135_VGPR136_VGPR137: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR135_VGPR136_VGPR137_VGPR138: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR136_VGPR137_VGPR138_VGPR139: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR137_VGPR138_VGPR139_VGPR140: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR138_VGPR139_VGPR140_VGPR141: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR139_VGPR140_VGPR141_VGPR142: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR140_VGPR141_VGPR142_VGPR143: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR141_VGPR142_VGPR143_VGPR144: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR142_VGPR143_VGPR144_VGPR145: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR143_VGPR144_VGPR145_VGPR146: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR144_VGPR145_VGPR146_VGPR147: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR145_VGPR146_VGPR147_VGPR148: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR146_VGPR147_VGPR148_VGPR149: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR147_VGPR148_VGPR149_VGPR150: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR148_VGPR149_VGPR150_VGPR151: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR149_VGPR150_VGPR151_VGPR152: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR150_VGPR151_VGPR152_VGPR153: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR151_VGPR152_VGPR153_VGPR154: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR152_VGPR153_VGPR154_VGPR155: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR153_VGPR154_VGPR155_VGPR156: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR154_VGPR155_VGPR156_VGPR157: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR155_VGPR156_VGPR157_VGPR158: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR156_VGPR157_VGPR158_VGPR159: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR157_VGPR158_VGPR159_VGPR160: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR158_VGPR159_VGPR160_VGPR161: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR159_VGPR160_VGPR161_VGPR162: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR160_VGPR161_VGPR162_VGPR163: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR161_VGPR162_VGPR163_VGPR164: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR162_VGPR163_VGPR164_VGPR165: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR163_VGPR164_VGPR165_VGPR166: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR164_VGPR165_VGPR166_VGPR167: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR165_VGPR166_VGPR167_VGPR168: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR166_VGPR167_VGPR168_VGPR169: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR167_VGPR168_VGPR169_VGPR170: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR168_VGPR169_VGPR170_VGPR171: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR169_VGPR170_VGPR171_VGPR172: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR170_VGPR171_VGPR172_VGPR173: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR171_VGPR172_VGPR173_VGPR174: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR172_VGPR173_VGPR174_VGPR175: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR173_VGPR174_VGPR175_VGPR176: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR174_VGPR175_VGPR176_VGPR177: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR175_VGPR176_VGPR177_VGPR178: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR176_VGPR177_VGPR178_VGPR179: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR177_VGPR178_VGPR179_VGPR180: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR178_VGPR179_VGPR180_VGPR181: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR179_VGPR180_VGPR181_VGPR182: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR180_VGPR181_VGPR182_VGPR183: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR181_VGPR182_VGPR183_VGPR184: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR182_VGPR183_VGPR184_VGPR185: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR183_VGPR184_VGPR185_VGPR186: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR184_VGPR185_VGPR186_VGPR187: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR185_VGPR186_VGPR187_VGPR188: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR186_VGPR187_VGPR188_VGPR189: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR187_VGPR188_VGPR189_VGPR190: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR188_VGPR189_VGPR190_VGPR191: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR189_VGPR190_VGPR191_VGPR192: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR190_VGPR191_VGPR192_VGPR193: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR191_VGPR192_VGPR193_VGPR194: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR192_VGPR193_VGPR194_VGPR195: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR193_VGPR194_VGPR195_VGPR196: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR194_VGPR195_VGPR196_VGPR197: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR195_VGPR196_VGPR197_VGPR198: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR196_VGPR197_VGPR198_VGPR199: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR197_VGPR198_VGPR199_VGPR200: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR198_VGPR199_VGPR200_VGPR201: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR199_VGPR200_VGPR201_VGPR202: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR200_VGPR201_VGPR202_VGPR203: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR201_VGPR202_VGPR203_VGPR204: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR202_VGPR203_VGPR204_VGPR205: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR203_VGPR204_VGPR205_VGPR206: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR204_VGPR205_VGPR206_VGPR207: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR205_VGPR206_VGPR207_VGPR208: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR206_VGPR207_VGPR208_VGPR209: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR207_VGPR208_VGPR209_VGPR210: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR208_VGPR209_VGPR210_VGPR211: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR209_VGPR210_VGPR211_VGPR212: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR210_VGPR211_VGPR212_VGPR213: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR211_VGPR212_VGPR213_VGPR214: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR212_VGPR213_VGPR214_VGPR215: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR213_VGPR214_VGPR215_VGPR216: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR214_VGPR215_VGPR216_VGPR217: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR215_VGPR216_VGPR217_VGPR218: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR216_VGPR217_VGPR218_VGPR219: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR217_VGPR218_VGPR219_VGPR220: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR218_VGPR219_VGPR220_VGPR221: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR219_VGPR220_VGPR221_VGPR222: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR220_VGPR221_VGPR222_VGPR223: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR221_VGPR222_VGPR223_VGPR224: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR222_VGPR223_VGPR224_VGPR225: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR223_VGPR224_VGPR225_VGPR226: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR224_VGPR225_VGPR226_VGPR227: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR225_VGPR226_VGPR227_VGPR228: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR226_VGPR227_VGPR228_VGPR229: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR227_VGPR228_VGPR229_VGPR230: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR228_VGPR229_VGPR230_VGPR231: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR229_VGPR230_VGPR231_VGPR232: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR230_VGPR231_VGPR232_VGPR233: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR231_VGPR232_VGPR233_VGPR234: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR232_VGPR233_VGPR234_VGPR235: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR233_VGPR234_VGPR235_VGPR236: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR234_VGPR235_VGPR236_VGPR237: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR235_VGPR236_VGPR237_VGPR238: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR236_VGPR237_VGPR238_VGPR239: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR237_VGPR238_VGPR239_VGPR240: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR238_VGPR239_VGPR240_VGPR241: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR239_VGPR240_VGPR241_VGPR242: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR240_VGPR241_VGPR242_VGPR243: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR241_VGPR242_VGPR243_VGPR244: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR242_VGPR243_VGPR244_VGPR245: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR243_VGPR244_VGPR245_VGPR246: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR244_VGPR245_VGPR246_VGPR247: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR245_VGPR246_VGPR247_VGPR248: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR246_VGPR247_VGPR248_VGPR249: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR247_VGPR248_VGPR249_VGPR250: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR248_VGPR249_VGPR250_VGPR251: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR249_VGPR250_VGPR251_VGPR252: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR250_VGPR251_VGPR252_VGPR253: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR251_VGPR252_VGPR253_VGPR254: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR252_VGPR253_VGPR254_VGPR255: OpKind = MCK_VReg_128; break;
    case AMDGPU::VGPR0_VGPR1_VGPR2_VGPR3_VGPR4_VGPR5_VGPR6_VGPR7: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR1_VGPR2_VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR2_VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252_VGPR253: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252_VGPR253_VGPR254: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR248_VGPR249_VGPR250_VGPR251_VGPR252_VGPR253_VGPR254_VGPR255: OpKind = MCK_VReg_256; break;
    case AMDGPU::VGPR0_VGPR1_VGPR2_VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR1_VGPR2_VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR2_VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR3_VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR4_VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR5_VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR6_VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR7_VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR8_VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR9_VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR10_VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR11_VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR12_VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR13_VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR14_VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR15_VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR16_VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR17_VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR18_VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR19_VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR20_VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR21_VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR22_VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR23_VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR24_VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR25_VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR26_VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR27_VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR28_VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR29_VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR30_VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR31_VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR32_VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR33_VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR34_VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR35_VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR36_VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR37_VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR38_VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR39_VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR40_VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR41_VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR42_VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR43_VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR44_VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR45_VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR46_VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR47_VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR48_VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR49_VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR50_VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR51_VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR52_VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR53_VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR54_VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR55_VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR56_VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR57_VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR58_VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR59_VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR60_VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR61_VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR62_VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR63_VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR64_VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR65_VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR66_VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR67_VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR68_VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR69_VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR70_VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR71_VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR72_VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR73_VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR74_VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR75_VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR76_VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR77_VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR78_VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR79_VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR80_VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR81_VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR82_VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR83_VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR84_VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR85_VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR86_VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR87_VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR88_VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR89_VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR90_VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR91_VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR92_VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR93_VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR94_VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR95_VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR96_VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR97_VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR98_VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR99_VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR100_VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR101_VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR102_VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR103_VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR104_VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR105_VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR106_VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR107_VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR108_VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR109_VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR110_VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR111_VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR112_VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR113_VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR114_VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR115_VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR116_VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR117_VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR118_VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR119_VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR120_VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR121_VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR122_VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR123_VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR124_VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR125_VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR126_VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR127_VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR128_VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR129_VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR130_VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR131_VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR132_VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR133_VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR134_VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR135_VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR136_VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR137_VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR138_VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR139_VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR140_VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR141_VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR142_VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR143_VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR144_VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR145_VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR146_VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR147_VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR148_VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR149_VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR150_VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR151_VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR152_VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR153_VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR154_VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR155_VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR156_VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR157_VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR158_VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR159_VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR160_VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR161_VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR162_VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR163_VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR164_VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR165_VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR166_VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR167_VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR168_VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR169_VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR170_VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR171_VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR172_VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR173_VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR174_VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR175_VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR176_VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR177_VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR178_VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR179_VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR180_VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR181_VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR182_VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR183_VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR184_VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR185_VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR186_VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR187_VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR188_VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR189_VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR190_VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR191_VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR192_VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR193_VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR194_VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR195_VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR196_VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR197_VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR198_VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR199_VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR200_VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR201_VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR202_VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR203_VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR204_VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR205_VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR206_VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR207_VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR208_VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR209_VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR210_VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR211_VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR212_VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR213_VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR214_VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR215_VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR216_VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR217_VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR218_VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR219_VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR220_VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR221_VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR222_VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR223_VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR224_VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR225_VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR226_VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR227_VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR228_VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR229_VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR230_VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR231_VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR232_VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR233_VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR234_VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR235_VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR236_VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR237_VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR238_VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252_VGPR253: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR239_VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252_VGPR253_VGPR254: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR240_VGPR241_VGPR242_VGPR243_VGPR244_VGPR245_VGPR246_VGPR247_VGPR248_VGPR249_VGPR250_VGPR251_VGPR252_VGPR253_VGPR254_VGPR255: OpKind = MCK_VReg_512; break;
    case AMDGPU::VGPR0_VGPR1: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR1_VGPR2: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR2_VGPR3: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR3_VGPR4: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR4_VGPR5: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR5_VGPR6: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR6_VGPR7: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR7_VGPR8: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR8_VGPR9: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR9_VGPR10: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR10_VGPR11: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR11_VGPR12: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR12_VGPR13: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR13_VGPR14: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR14_VGPR15: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR15_VGPR16: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR16_VGPR17: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR17_VGPR18: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR18_VGPR19: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR19_VGPR20: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR20_VGPR21: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR21_VGPR22: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR22_VGPR23: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR23_VGPR24: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR24_VGPR25: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR25_VGPR26: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR26_VGPR27: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR27_VGPR28: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR28_VGPR29: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR29_VGPR30: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR30_VGPR31: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR31_VGPR32: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR32_VGPR33: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR33_VGPR34: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR34_VGPR35: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR35_VGPR36: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR36_VGPR37: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR37_VGPR38: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR38_VGPR39: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR39_VGPR40: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR40_VGPR41: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR41_VGPR42: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR42_VGPR43: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR43_VGPR44: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR44_VGPR45: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR45_VGPR46: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR46_VGPR47: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR47_VGPR48: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR48_VGPR49: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR49_VGPR50: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR50_VGPR51: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR51_VGPR52: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR52_VGPR53: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR53_VGPR54: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR54_VGPR55: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR55_VGPR56: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR56_VGPR57: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR57_VGPR58: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR58_VGPR59: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR59_VGPR60: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR60_VGPR61: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR61_VGPR62: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR62_VGPR63: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR63_VGPR64: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR64_VGPR65: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR65_VGPR66: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR66_VGPR67: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR67_VGPR68: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR68_VGPR69: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR69_VGPR70: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR70_VGPR71: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR71_VGPR72: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR72_VGPR73: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR73_VGPR74: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR74_VGPR75: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR75_VGPR76: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR76_VGPR77: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR77_VGPR78: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR78_VGPR79: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR79_VGPR80: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR80_VGPR81: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR81_VGPR82: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR82_VGPR83: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR83_VGPR84: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR84_VGPR85: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR85_VGPR86: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR86_VGPR87: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR87_VGPR88: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR88_VGPR89: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR89_VGPR90: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR90_VGPR91: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR91_VGPR92: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR92_VGPR93: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR93_VGPR94: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR94_VGPR95: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR95_VGPR96: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR96_VGPR97: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR97_VGPR98: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR98_VGPR99: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR99_VGPR100: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR100_VGPR101: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR101_VGPR102: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR102_VGPR103: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR103_VGPR104: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR104_VGPR105: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR105_VGPR106: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR106_VGPR107: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR107_VGPR108: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR108_VGPR109: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR109_VGPR110: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR110_VGPR111: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR111_VGPR112: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR112_VGPR113: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR113_VGPR114: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR114_VGPR115: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR115_VGPR116: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR116_VGPR117: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR117_VGPR118: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR118_VGPR119: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR119_VGPR120: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR120_VGPR121: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR121_VGPR122: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR122_VGPR123: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR123_VGPR124: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR124_VGPR125: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR125_VGPR126: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR126_VGPR127: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR127_VGPR128: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR128_VGPR129: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR129_VGPR130: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR130_VGPR131: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR131_VGPR132: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR132_VGPR133: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR133_VGPR134: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR134_VGPR135: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR135_VGPR136: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR136_VGPR137: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR137_VGPR138: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR138_VGPR139: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR139_VGPR140: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR140_VGPR141: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR141_VGPR142: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR142_VGPR143: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR143_VGPR144: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR144_VGPR145: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR145_VGPR146: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR146_VGPR147: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR147_VGPR148: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR148_VGPR149: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR149_VGPR150: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR150_VGPR151: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR151_VGPR152: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR152_VGPR153: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR153_VGPR154: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR154_VGPR155: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR155_VGPR156: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR156_VGPR157: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR157_VGPR158: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR158_VGPR159: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR159_VGPR160: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR160_VGPR161: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR161_VGPR162: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR162_VGPR163: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR163_VGPR164: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR164_VGPR165: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR165_VGPR166: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR166_VGPR167: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR167_VGPR168: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR168_VGPR169: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR169_VGPR170: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR170_VGPR171: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR171_VGPR172: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR172_VGPR173: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR173_VGPR174: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR174_VGPR175: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR175_VGPR176: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR176_VGPR177: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR177_VGPR178: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR178_VGPR179: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR179_VGPR180: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR180_VGPR181: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR181_VGPR182: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR182_VGPR183: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR183_VGPR184: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR184_VGPR185: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR185_VGPR186: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR186_VGPR187: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR187_VGPR188: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR188_VGPR189: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR189_VGPR190: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR190_VGPR191: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR191_VGPR192: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR192_VGPR193: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR193_VGPR194: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR194_VGPR195: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR195_VGPR196: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR196_VGPR197: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR197_VGPR198: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR198_VGPR199: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR199_VGPR200: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR200_VGPR201: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR201_VGPR202: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR202_VGPR203: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR203_VGPR204: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR204_VGPR205: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR205_VGPR206: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR206_VGPR207: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR207_VGPR208: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR208_VGPR209: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR209_VGPR210: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR210_VGPR211: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR211_VGPR212: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR212_VGPR213: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR213_VGPR214: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR214_VGPR215: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR215_VGPR216: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR216_VGPR217: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR217_VGPR218: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR218_VGPR219: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR219_VGPR220: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR220_VGPR221: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR221_VGPR222: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR222_VGPR223: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR223_VGPR224: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR224_VGPR225: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR225_VGPR226: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR226_VGPR227: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR227_VGPR228: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR228_VGPR229: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR229_VGPR230: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR230_VGPR231: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR231_VGPR232: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR232_VGPR233: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR233_VGPR234: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR234_VGPR235: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR235_VGPR236: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR236_VGPR237: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR237_VGPR238: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR238_VGPR239: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR239_VGPR240: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR240_VGPR241: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR241_VGPR242: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR242_VGPR243: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR243_VGPR244: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR244_VGPR245: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR245_VGPR246: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR246_VGPR247: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR247_VGPR248: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR248_VGPR249: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR249_VGPR250: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR250_VGPR251: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR251_VGPR252: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR252_VGPR253: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR253_VGPR254: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR254_VGPR255: OpKind = MCK_VReg_64; break;
    case AMDGPU::VGPR0_VGPR1_VGPR2: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR1_VGPR2_VGPR3: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR2_VGPR3_VGPR4: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR3_VGPR4_VGPR5: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR4_VGPR5_VGPR6: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR5_VGPR6_VGPR7: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR6_VGPR7_VGPR8: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR7_VGPR8_VGPR9: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR8_VGPR9_VGPR10: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR9_VGPR10_VGPR11: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR10_VGPR11_VGPR12: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR11_VGPR12_VGPR13: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR12_VGPR13_VGPR14: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR13_VGPR14_VGPR15: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR14_VGPR15_VGPR16: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR15_VGPR16_VGPR17: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR16_VGPR17_VGPR18: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR17_VGPR18_VGPR19: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR18_VGPR19_VGPR20: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR19_VGPR20_VGPR21: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR20_VGPR21_VGPR22: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR21_VGPR22_VGPR23: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR22_VGPR23_VGPR24: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR23_VGPR24_VGPR25: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR24_VGPR25_VGPR26: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR25_VGPR26_VGPR27: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR26_VGPR27_VGPR28: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR27_VGPR28_VGPR29: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR28_VGPR29_VGPR30: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR29_VGPR30_VGPR31: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR30_VGPR31_VGPR32: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR31_VGPR32_VGPR33: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR32_VGPR33_VGPR34: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR33_VGPR34_VGPR35: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR34_VGPR35_VGPR36: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR35_VGPR36_VGPR37: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR36_VGPR37_VGPR38: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR37_VGPR38_VGPR39: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR38_VGPR39_VGPR40: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR39_VGPR40_VGPR41: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR40_VGPR41_VGPR42: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR41_VGPR42_VGPR43: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR42_VGPR43_VGPR44: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR43_VGPR44_VGPR45: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR44_VGPR45_VGPR46: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR45_VGPR46_VGPR47: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR46_VGPR47_VGPR48: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR47_VGPR48_VGPR49: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR48_VGPR49_VGPR50: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR49_VGPR50_VGPR51: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR50_VGPR51_VGPR52: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR51_VGPR52_VGPR53: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR52_VGPR53_VGPR54: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR53_VGPR54_VGPR55: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR54_VGPR55_VGPR56: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR55_VGPR56_VGPR57: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR56_VGPR57_VGPR58: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR57_VGPR58_VGPR59: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR58_VGPR59_VGPR60: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR59_VGPR60_VGPR61: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR60_VGPR61_VGPR62: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR61_VGPR62_VGPR63: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR62_VGPR63_VGPR64: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR63_VGPR64_VGPR65: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR64_VGPR65_VGPR66: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR65_VGPR66_VGPR67: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR66_VGPR67_VGPR68: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR67_VGPR68_VGPR69: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR68_VGPR69_VGPR70: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR69_VGPR70_VGPR71: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR70_VGPR71_VGPR72: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR71_VGPR72_VGPR73: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR72_VGPR73_VGPR74: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR73_VGPR74_VGPR75: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR74_VGPR75_VGPR76: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR75_VGPR76_VGPR77: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR76_VGPR77_VGPR78: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR77_VGPR78_VGPR79: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR78_VGPR79_VGPR80: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR79_VGPR80_VGPR81: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR80_VGPR81_VGPR82: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR81_VGPR82_VGPR83: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR82_VGPR83_VGPR84: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR83_VGPR84_VGPR85: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR84_VGPR85_VGPR86: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR85_VGPR86_VGPR87: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR86_VGPR87_VGPR88: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR87_VGPR88_VGPR89: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR88_VGPR89_VGPR90: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR89_VGPR90_VGPR91: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR90_VGPR91_VGPR92: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR91_VGPR92_VGPR93: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR92_VGPR93_VGPR94: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR93_VGPR94_VGPR95: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR94_VGPR95_VGPR96: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR95_VGPR96_VGPR97: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR96_VGPR97_VGPR98: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR97_VGPR98_VGPR99: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR98_VGPR99_VGPR100: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR99_VGPR100_VGPR101: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR100_VGPR101_VGPR102: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR101_VGPR102_VGPR103: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR102_VGPR103_VGPR104: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR103_VGPR104_VGPR105: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR104_VGPR105_VGPR106: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR105_VGPR106_VGPR107: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR106_VGPR107_VGPR108: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR107_VGPR108_VGPR109: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR108_VGPR109_VGPR110: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR109_VGPR110_VGPR111: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR110_VGPR111_VGPR112: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR111_VGPR112_VGPR113: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR112_VGPR113_VGPR114: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR113_VGPR114_VGPR115: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR114_VGPR115_VGPR116: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR115_VGPR116_VGPR117: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR116_VGPR117_VGPR118: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR117_VGPR118_VGPR119: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR118_VGPR119_VGPR120: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR119_VGPR120_VGPR121: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR120_VGPR121_VGPR122: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR121_VGPR122_VGPR123: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR122_VGPR123_VGPR124: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR123_VGPR124_VGPR125: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR124_VGPR125_VGPR126: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR125_VGPR126_VGPR127: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR126_VGPR127_VGPR128: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR127_VGPR128_VGPR129: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR128_VGPR129_VGPR130: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR129_VGPR130_VGPR131: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR130_VGPR131_VGPR132: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR131_VGPR132_VGPR133: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR132_VGPR133_VGPR134: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR133_VGPR134_VGPR135: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR134_VGPR135_VGPR136: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR135_VGPR136_VGPR137: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR136_VGPR137_VGPR138: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR137_VGPR138_VGPR139: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR138_VGPR139_VGPR140: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR139_VGPR140_VGPR141: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR140_VGPR141_VGPR142: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR141_VGPR142_VGPR143: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR142_VGPR143_VGPR144: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR143_VGPR144_VGPR145: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR144_VGPR145_VGPR146: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR145_VGPR146_VGPR147: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR146_VGPR147_VGPR148: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR147_VGPR148_VGPR149: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR148_VGPR149_VGPR150: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR149_VGPR150_VGPR151: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR150_VGPR151_VGPR152: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR151_VGPR152_VGPR153: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR152_VGPR153_VGPR154: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR153_VGPR154_VGPR155: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR154_VGPR155_VGPR156: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR155_VGPR156_VGPR157: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR156_VGPR157_VGPR158: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR157_VGPR158_VGPR159: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR158_VGPR159_VGPR160: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR159_VGPR160_VGPR161: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR160_VGPR161_VGPR162: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR161_VGPR162_VGPR163: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR162_VGPR163_VGPR164: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR163_VGPR164_VGPR165: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR164_VGPR165_VGPR166: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR165_VGPR166_VGPR167: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR166_VGPR167_VGPR168: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR167_VGPR168_VGPR169: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR168_VGPR169_VGPR170: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR169_VGPR170_VGPR171: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR170_VGPR171_VGPR172: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR171_VGPR172_VGPR173: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR172_VGPR173_VGPR174: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR173_VGPR174_VGPR175: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR174_VGPR175_VGPR176: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR175_VGPR176_VGPR177: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR176_VGPR177_VGPR178: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR177_VGPR178_VGPR179: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR178_VGPR179_VGPR180: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR179_VGPR180_VGPR181: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR180_VGPR181_VGPR182: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR181_VGPR182_VGPR183: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR182_VGPR183_VGPR184: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR183_VGPR184_VGPR185: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR184_VGPR185_VGPR186: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR185_VGPR186_VGPR187: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR186_VGPR187_VGPR188: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR187_VGPR188_VGPR189: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR188_VGPR189_VGPR190: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR189_VGPR190_VGPR191: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR190_VGPR191_VGPR192: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR191_VGPR192_VGPR193: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR192_VGPR193_VGPR194: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR193_VGPR194_VGPR195: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR194_VGPR195_VGPR196: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR195_VGPR196_VGPR197: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR196_VGPR197_VGPR198: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR197_VGPR198_VGPR199: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR198_VGPR199_VGPR200: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR199_VGPR200_VGPR201: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR200_VGPR201_VGPR202: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR201_VGPR202_VGPR203: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR202_VGPR203_VGPR204: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR203_VGPR204_VGPR205: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR204_VGPR205_VGPR206: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR205_VGPR206_VGPR207: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR206_VGPR207_VGPR208: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR207_VGPR208_VGPR209: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR208_VGPR209_VGPR210: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR209_VGPR210_VGPR211: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR210_VGPR211_VGPR212: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR211_VGPR212_VGPR213: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR212_VGPR213_VGPR214: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR213_VGPR214_VGPR215: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR214_VGPR215_VGPR216: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR215_VGPR216_VGPR217: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR216_VGPR217_VGPR218: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR217_VGPR218_VGPR219: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR218_VGPR219_VGPR220: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR219_VGPR220_VGPR221: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR220_VGPR221_VGPR222: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR221_VGPR222_VGPR223: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR222_VGPR223_VGPR224: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR223_VGPR224_VGPR225: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR224_VGPR225_VGPR226: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR225_VGPR226_VGPR227: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR226_VGPR227_VGPR228: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR227_VGPR228_VGPR229: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR228_VGPR229_VGPR230: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR229_VGPR230_VGPR231: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR230_VGPR231_VGPR232: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR231_VGPR232_VGPR233: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR232_VGPR233_VGPR234: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR233_VGPR234_VGPR235: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR234_VGPR235_VGPR236: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR235_VGPR236_VGPR237: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR236_VGPR237_VGPR238: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR237_VGPR238_VGPR239: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR238_VGPR239_VGPR240: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR239_VGPR240_VGPR241: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR240_VGPR241_VGPR242: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR241_VGPR242_VGPR243: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR242_VGPR243_VGPR244: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR243_VGPR244_VGPR245: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR244_VGPR245_VGPR246: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR245_VGPR246_VGPR247: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR246_VGPR247_VGPR248: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR247_VGPR248_VGPR249: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR248_VGPR249_VGPR250: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR249_VGPR250_VGPR251: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR250_VGPR251_VGPR252: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR251_VGPR252_VGPR253: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR252_VGPR253_VGPR254: OpKind = MCK_VReg_96; break;
    case AMDGPU::VGPR253_VGPR254_VGPR255: OpKind = MCK_VReg_96; break;
    }
    return isSubclass(OpKind, Kind) ? MCTargetAsmParser::Match_Success :
                                      MCTargetAsmParser::Match_InvalidOperand;
  }

  return MCTargetAsmParser::Match_InvalidOperand;
}

uint64_t AMDGPUAsmParser::
ComputeAvailableFeatures(uint64_t FB) const {
  uint64_t Features = 0;
  return Features;
}

static const char *const MnemonicTable =
    "\ts_barrier\010s_branch\020s_cbranch_execnz\017s_cbranch_execz\016s_cbr"
    "anch_scc0\016s_cbranch_scc1\017s_cbranch_vccnz\016s_cbranch_vccz\016s_d"
    "ecperflevel\010s_endpgm\014s_icache_inv\016s_incperflevel\005s_nop\ts_s"
    "endmsg\015s_sendmsghalt\ts_sethalt\ts_setprio\007s_sleep\006s_trap\014s"
    "_ttracedata\ts_waitcnt";

namespace {
  struct MatchEntry {
    uint8_t Mnemonic;
    uint16_t Opcode;
    uint8_t ConvertFn;
    uint8_t RequiredFeatures;
    uint8_t Classes[1];
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
  { 0 /* s_barrier */, AMDGPU::S_BARRIER, Convert_NoOperands, 0, {  }, },
  { 10 /* s_branch */, AMDGPU::S_BRANCH, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 19 /* s_cbranch_execnz */, AMDGPU::S_CBRANCH_EXECNZ, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 36 /* s_cbranch_execz */, AMDGPU::S_CBRANCH_EXECZ, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 52 /* s_cbranch_scc0 */, AMDGPU::S_CBRANCH_SCC0, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 67 /* s_cbranch_scc1 */, AMDGPU::S_CBRANCH_SCC1, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 82 /* s_cbranch_vccnz */, AMDGPU::S_CBRANCH_VCCNZ, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 98 /* s_cbranch_vccz */, AMDGPU::S_CBRANCH_VCCZ, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 113 /* s_decperflevel */, AMDGPU::S_DECPERFLEVEL, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 128 /* s_endpgm */, AMDGPU::S_ENDPGM, Convert_NoOperands, 0, {  }, },
  { 137 /* s_icache_inv */, AMDGPU::S_ICACHE_INV, Convert_NoOperands, 0, {  }, },
  { 150 /* s_incperflevel */, AMDGPU::S_INCPERFLEVEL, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 165 /* s_nop */, AMDGPU::S_NOP, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 171 /* s_sendmsg */, AMDGPU::S_SENDMSG, Convert__Imm1_0__imm_0, 0, { MCK_Imm }, },
  { 181 /* s_sendmsghalt */, AMDGPU::S_SENDMSGHALT, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 195 /* s_sethalt */, AMDGPU::S_SETHALT, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 205 /* s_setprio */, AMDGPU::S_SETPRIO, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 215 /* s_sleep */, AMDGPU::S_SLEEP, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 223 /* s_trap */, AMDGPU::S_TRAP, Convert__Imm1_0, 0, { MCK_Imm }, },
  { 230 /* s_ttracedata */, AMDGPU::S_TTRACEDATA, Convert_NoOperands, 0, {  }, },
  { 243 /* s_waitcnt */, AMDGPU::S_WAITCNT, Convert__SWaitCnt1_0, 0, { MCK_SWaitCnt }, },
};

bool AMDGPUAsmParser::
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

unsigned AMDGPUAsmParser::
MatchInstructionImpl(const OperandVector &Operands,
                     MCInst &Inst, uint64_t &ErrorInfo,
                     bool matchingInlineAsm, unsigned VariantID) {
  // Eliminate obvious mismatches.
  if (Operands.size() > 2) {
    ErrorInfo = 2;
    return Match_InvalidOperand;
  }

  // Get the current feature set.
  uint64_t AvailableFeatures = getAvailableFeatures();

  // Get the instruction mnemonic, which is the first token.
  StringRef Mnemonic = ((AMDGPUOperand&)*Operands[0]).getToken();

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
    for (unsigned i = 0; i != 1; ++i) {
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

    return Match_Success;
  }

  // Okay, we had no match.  Try to return a useful error code.
  if (HadMatchOtherThanPredicate || !HadMatchOtherThanFeatures)
    return RetCode;

  // Missing feature matches return which features were missing
  ErrorInfo = MissingFeatures;
  return Match_MissingFeature;
}

namespace {
  struct OperandMatchEntry {
    uint8_t RequiredFeatures;
    uint8_t Mnemonic;
    uint8_t Class;
    uint8_t OperandMask;

    StringRef getMnemonic() const {
      return StringRef(MnemonicTable + Mnemonic + 1,
                       MnemonicTable[Mnemonic]);
    }
  };

  // Predicate for searching for an opcode.
  struct LessOpcodeOperand {
    bool operator()(const OperandMatchEntry &LHS, StringRef RHS) {
      return LHS.getMnemonic()  < RHS;
    }
    bool operator()(StringRef LHS, const OperandMatchEntry &RHS) {
      return LHS < RHS.getMnemonic();
    }
    bool operator()(const OperandMatchEntry &LHS, const OperandMatchEntry &RHS) {
      return LHS.getMnemonic() < RHS.getMnemonic();
    }
  };
} // end anonymous namespace.

static const OperandMatchEntry OperandMatchTable[1] = {
  /* Operand List Mask, Mnemonic, Operand Class, Features */
  { 0, 243 /* s_waitcnt */, MCK_SWaitCnt, 1 /* 0 */ },
};

AMDGPUAsmParser::OperandMatchResultTy AMDGPUAsmParser::
tryCustomParseOperand(OperandVector &Operands,
                      unsigned MCK) {

  switch(MCK) {
  case MCK_SWaitCnt:
    return parseSWaitCntOps(Operands);
  default:
    return MatchOperand_NoMatch;
  }
  return MatchOperand_NoMatch;
}

AMDGPUAsmParser::OperandMatchResultTy AMDGPUAsmParser::
MatchOperandParserImpl(OperandVector &Operands,
                       StringRef Mnemonic) {
  // Get the current feature set.
  uint64_t AvailableFeatures = getAvailableFeatures();

  // Get the next operand index.
  unsigned NextOpNum = Operands.size()-1;
  // Search the table.
  std::pair<const OperandMatchEntry*, const OperandMatchEntry*> MnemonicRange =
    std::equal_range(OperandMatchTable, OperandMatchTable+1, Mnemonic,
                     LessOpcodeOperand());

  if (MnemonicRange.first == MnemonicRange.second)
    return MatchOperand_NoMatch;

  for (const OperandMatchEntry *it = MnemonicRange.first,
       *ie = MnemonicRange.second; it != ie; ++it) {
    // equal_range guarantees that instruction mnemonic matches.
    assert(Mnemonic == it->getMnemonic());

    // check if the available features match
    if ((AvailableFeatures & it->RequiredFeatures) != it->RequiredFeatures) {
      continue;
    }

    // check if the operand in question has a custom parser.
    if (!(it->OperandMask & (1 << NextOpNum)))
      continue;

    // call custom parse method to handle the operand
    OperandMatchResultTy Result = tryCustomParseOperand(Operands, it->Class);
    if (Result != MatchOperand_NoMatch)
      return Result;
  }

  // Okay, we had no match.
  return MatchOperand_NoMatch;
}

#endif // GET_MATCHER_IMPLEMENTATION

