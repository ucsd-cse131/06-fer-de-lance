{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.FDL.Compiler ( compiler, compile ) where

import           Control.Arrow                    ((>>>))
import           Prelude                  hiding (compare)
import           Control.Monad                   (void)
import           Data.Maybe
import           Data.Bits                       (shift)
import qualified Data.Set                as S
import           Language.FDL.Types      hiding (Tag)
import           Language.FDL.Parser     (parse)
import           Language.FDL.Checker    (check, errUnboundVar)
import           Language.FDL.Normalizer (anormal)
import           Language.FDL.Asm        (asm)
import qualified Language.FDL.Utils     as U


--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> compile >>> asm

--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Tag@
--------------------------------------------------------------------------------
type Ann   = (SourceSpan, Int)
type AExp  = AnfExpr Ann
type IExp  = ImmExpr Ann
type ABind = Bind    Ann

instance Located Ann where
  sourceSpan = fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

annTag :: Ann -> Int
annTag = snd 


--------------------------------------------------------------------------------
-- | @tag@ annotates each AST node with a distinct Int value
--------------------------------------------------------------------------------
tag :: AnfExpr SourceSpan -> AExp
--------------------------------------------------------------------------------
tag = label

--------------------------------------------------------------------------------
compile :: AExp -> [Instruction]
--------------------------------------------------------------------------------
compile e = compileDecl Nothing [] [] e

{- | @compileDecl f xs body@ returns the instructions of `body` 
     of a function with optional name 'f', parameters 'xs', and 
     free variables 'ys'. The instructions should:

     1. setup  stack frame RBP/RSP
     2. copy parameters (following x86-64 call convention) to stack slots
     3. copy (closure) free vars (from tuple at RDI) to stack slots
     4. execute 'body' with result in RAX
     5. teardown stack frame & return 

     @name@ is the (optional) name of the function, that may be useful to implement recursion.
-} 
compileDecl :: Maybe ABind -> [Id] -> [ABind] -> AExp -> [Instruction]
compileDecl f ys xs body =
  error "fill this in"

declId :: Maybe (Bind a) -> Id
declId Nothing  = "$self"
declId (Just f) = bindId f 

-- | @compileArgs xs@ returns the instructions needed to copy the parameter values
--   FROM the combination of `rdi`, `rsi`, ... INTO this function's "frame".
--   RDI -> [RBP - 8], RSI -> [RBP - 16] 
copyArgs :: [a] -> [Instruction]
copyArgs xs =  
  error "fill this in"

-- FILL: insert instructions for setting up stack for `n` local vars
funEntry :: Int -> [Instruction]
funEntry n = 
  error "fill this in"

-- FILL: clean up stack & labels for jumping to error
funExit :: Int -> [Instruction]
funExit n = 
  error "fill this in"

-- | @restore ys@ uses the closure passed in at RDI to copy the 
--  free-vars 'ys' onto the stack starting at 'base' (after the params)
restore :: Int -> [Id] -> [Instruction]
restore base ys = 
  error "fill this in"

lambda :: Ann -> Env -> Maybe ABind -> [ABind] -> AExp -> [Instruction]
lambda l env f xs e
  = IJmp   end   
  : ILabel start 
  : compileDecl f ys xs e
 ++ ILabel end 
  : lambdaClosure l env arity start ys
  where
    ys    = freeVars (fun f xs e l)
    arity = length xs
    (start, end) = startEnd (snd l) f

startEnd :: Int -> Maybe ABind -> (Label, Label) 
startEnd i Nothing           = (LamStart i, LamEnd i) 
startEnd i (Just (Bind f _)) = (DefFun f i, DefEnd f i)

{- | @lambdaClosure l env arity ys@ returns a sequence of instructions,
     that have the effect of writing into RAX the value of the closure
     corresponding to the lambda-functiion l. To do so we must:
  
     1. allocate space on the tuple for a "tuple" of
          (arity, LamStart l, y1, y2, ... , yn) 

     2. write the values of arity, y1...yn into the above

     3. adjust the address bits to ensure 101-ending
-}

lambdaClosure :: Ann -> Env -> Int -> Label -> [Id] -> [Instruction]
lambdaClosure l env arity start ys =  
  error "fill this in"

roundUp :: Int -> Int
roundUp n = if even n then n else n + 1

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e) (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
freeVars :: Expr a -> [Id]
--------------------------------------------------------------------------------
freeVars e = 
  error "fill this in"

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@Number {}     = [ compileImm env v  ]

compileEnv env v@Boolean {}    = [ compileImm env v  ]

compileEnv env v@Id {}         = [ compileImm env v  ]

compileEnv env e@Let {}        = is ++ compileEnv env' body
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = error "fill this in"

compileEnv env (Tuple es _)      = error "fill this in"
compileEnv env (GetItem vE vI _) = error "fill this in"

compileEnv env (Lam xs e l)      = lambda l env Nothing xs  e
compileEnv env (Fun f xs e l)    = lambda l env (Just f) xs e
compileEnv env (App v vs l)      = error "fill this in"



compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg RAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is ++ is') bs
  where
    (env', is')            = compileBind env b

compileBind :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar i) (Reg RAX)]
    (i, env')          = pushEnv x env

compilePrim1 :: Ann -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1   v = error "fill this in"
compilePrim1 l env Sub1   v = error "fill this in"
compilePrim1 l env IsNum  v = error "fill this in"
compilePrim1 l env IsBool v = error "fill this in"
compilePrim1 _ env Print  v = error "fill this in"
compilePrim1 l env IsTuple v = error "fill this in"

compilePrim2 :: Ann -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
compilePrim2 _ env Plus    = error "fill this in"
compilePrim2 _ env Minus   = error "fill this in"
compilePrim2 _ env Times   = error "fill this in"
compilePrim2 l env Less    = error "fill this in"
compilePrim2 l env Greater = error "fill this in"
compilePrim2 l env Equal   = error "fill this in"

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " ++ show (void e)

stackVar :: Int -> Arg
stackVar i = RegOffset i RBP



--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001
typeTag TClosure  = HexConst 0x00000005

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007
typeMask TClosure = HexConst 0x00000007
