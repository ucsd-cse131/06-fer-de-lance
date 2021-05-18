module Language.FDL.Asm (asm) where

import qualified Data.List as L
import           Text.Printf (printf)
import           Language.FDL.Types

--------------------------------------------------------------------------------
-- | Convert a sequence of x86 `Instructions` into the output assembly
--------------------------------------------------------------------------------
asm :: [Instruction] -> Text
--------------------------------------------------------------------------------
asm instrs = header
          <> instrsAsm (prelude ++ instrs ++ postlude)
          <> "\n"

instrsAsm :: [Instruction] -> Text
instrsAsm = L.intercalate "\n" . map instrAsm

header :: Text
header = unlines
  [ "section .text"
  , "extern error"
  , "extern print"
  , "global our_code_starts_here"
  , "our_code_starts_here:"
  ]

prelude :: [Instruction]
prelude =
  [ -- setup regMask
    IMov regMask (HexConst 0xFFFFFFFF)
  , IShl regMask (Const 32) 
  , IOr  regMask (HexConst 0xFFFFFFF8)
  -- setup regData
  , IMov regData (Reg RDI)
  , IAdd regData (Const 8)
  , IAnd regData regMask
  ]


postlude :: [Instruction]
postlude = 
  concat
    [ dynError (TypeError TNumber)
    , dynError (TypeError TBoolean)
    , dynError (TypeError TTuple)
    , dynError (TypeError TClosure)
    , dynError ArithOverflow
    , dynError IndexLow
    , dynError IndexHigh
    , dynError ArityError
    ]

dynError   :: DynError -> [Instruction]
dynError e =
  error "fill this in"

--------------------------------------------------------------------------------
instrAsm :: Instruction -> Text
--------------------------------------------------------------------------------
instrAsm (IMov dst val) = printf "  mov %s, %s"  (argAsm dst) (argAsm val)
instrAsm (IAdd dst val) = printf "  add %s, %s"  (argAsm dst) (argAsm val)
instrAsm (ISub dst val) = printf "  sub %s, %s"  (argAsm dst) (argAsm val)
instrAsm (IMul dst val) = printf "  imul %s, %s" (argAsm dst) (argAsm val)
instrAsm (IAnd dst msk) = printf "  and %s, %s"  (argAsm dst) (argAsm msk)
instrAsm (IOr  dst msk) = printf "  or  %s, %s"  (argAsm dst) (argAsm msk)
instrAsm (IXor dst msk) = printf "  xor %s, %s"  (argAsm dst) (argAsm msk)
instrAsm (IShl dst val) = printf "  shl %s, %s"  (argAsm dst) (argAsm val)
instrAsm (IShr dst val) = printf "  shr %s, %s"  (argAsm dst) (argAsm val)
instrAsm (ISar dst val) = printf "  sar %s, %s"  (argAsm dst) (argAsm val)
instrAsm (ICmp a1 a2)   = printf "  cmp %s, %s"  (argAsm a1)  (argAsm a2)
instrAsm (IPush a)      = printf "  push %s"     (argAsm a)
instrAsm (IPop a)       = printf "  pop  %s"     (argAsm a)
instrAsm (ICall a)      = printf "  call %s"     (argAsm a)
instrAsm (ILabel l)     = printf "%s: "          (labelAsm l)
instrAsm (IJe  l)       = printf "  je  near %s" (labelAsm l)
instrAsm (IJne  l)      = printf "  jne near %s" (labelAsm l)
instrAsm (IJg  l)       = printf "  jg  near %s" (labelAsm l)
instrAsm (IJl  l)       = printf "  jl  near %s" (labelAsm l)
instrAsm (IJo  l)       = printf "  jo  near %s" (labelAsm l)
instrAsm (IJmp l)       = printf "  jmp near %s" (labelAsm l)
instrAsm IRet           =        "  ret"

regAsm :: Reg -> Text
regAsm RAX = "rax"
regAsm RBX = "rbx"
regAsm RSP = "rsp"
regAsm RBP = "rbp"
regAsm RSI = "rsi"
regAsm RDI = "rdi"
regAsm RDX = "rdx"
regAsm RCX = "rcx"
regAsm R8  = "r8"
regAsm R9  = "r9"
regAsm R14 = "r14"
regAsm R15 = "r15"

sizeAsm :: Size -> Text
sizeAsm QWordPtr = "QWORD"
sizeAsm DWordPtr = "DWORD"
sizeAsm WordPtr  = "WORD"
sizeAsm BytePtr  = "BYTE"

argAsm :: Arg -> Text
argAsm (Const n)       = printf "%d" n
argAsm (HexConst n)    = printf "0x%X" n
argAsm (Reg r)         = regAsm r
argAsm (RegOffset n r)
  | 0 <= n             = printf "[%s - %d]" (regAsm r) (8 * n)
  | otherwise          = printf "[%s + %d]" (regAsm r) (8 * negate n)
argAsm (RegIndex r i)  = printf "[%s + %s * 8]" (regAsm r) (regAsm i)
argAsm (Sized s a)     = printf "%s %s"     (sizeAsm s) (argAsm a)
argAsm (CodePtr l)     = labelAsm l

labelAsm :: Label -> Text
labelAsm (BranchTrue i) = printf "label_%d_true"      i
labelAsm (BranchDone i) = printf "label_%d_done"      i
labelAsm (LamStart   i) = printf "label_%d_lam_start" i
labelAsm (LamEnd     i) = printf "label_%d_lam_end"   i
labelAsm (DefFun f   i) = printf "label_%d_def_%s_start"  i f
labelAsm (DefFunBody f i) = printf "label_%d_def_%s_body" i f
labelAsm (DefEnd   f i) = printf "label_%d_def_%s_end"  i f

labelAsm (DynamicErr e) = dynErrorLabel e
labelAsm (Builtin f)    = f

_idLabel :: Id -> Text
_idLabel f = "fun_" ++ f

dynErrorLabel :: DynError -> Text
dynErrorLabel (TypeError t) = errorLabel ("non_" <> pprint t)
dynErrorLabel ArithOverflow = errorLabel "overflow"
dynErrorLabel IndexLow      = errorLabel "index_too_low"
dynErrorLabel IndexHigh     = errorLabel "index_too_high"
dynErrorLabel ArityError    = errorLabel "wrong_arity"

errorLabel :: Text -> Text
errorLabel l = "internal_error_" <> l -- errorFun l
