module Vega.Compile.Lua (compile) where

-- Super simple compilation to lua. This is mostly meant as a sanity check.
-- The actual native code backend is going to come later

import Vega.Prelude
import Vega.Syntax

import Vega.Name qualified as Name
-- TODO: We can technically use Eval for partial evaluation here!
import Vega.Eval
import Vega.Name (freshNameIO)

newtype Compile a = MkCompile (IO a)
    deriving (Functor, Applicative, Monad)

runCompile :: Compile a -> IO a
runCompile (MkCompile io) = io

freshName :: Text -> Compile Name
freshName name = MkCompile (freshNameIO name)

compile :: Vector CoreDeclaration -> IO Text
compile declarations = runCompile do
    declCode <- traverse compileDeclaration declarations
    pure $ definitions <> "\n\n" <> intercalate "\n\n" declCode

definitions :: Text
definitions = unlines [
        "function debugToString(x)"
    ,   "    if type(x) == \"string\" then"
    ,   "        return \"\\\"\" .. x .. \"\\\"\""
    ,   "    elseif type(x) == \"table\" then"
    ,   "        local arrayLike = true"
    ,   "        for key, _ in pairs(x) do"
    ,   "            if type(key) ~= \"number\" then"
    ,   "                arrayLike = false"
    ,   "                break"
    ,   "            end"
    ,   "        end"
    ,   "        if arrayLike then"
    ,   "            local str = \"(\""
    ,   "            for i, value in ipairs(x) do"
    ,   "                if (i ~= 1) then"
    ,   "                    str = str .. \", \""
    ,   "                end"
    ,   "                str = str .. debugToString(value)"
    ,   "            end"
    ,   "            return str .. \")\""
    ,   "        else"
    ,   "            local isInitial = true"
    ,   "            local str = \"{\""
    ,   "            for key, value in pairs(x) do"
    ,   "                if not isInitial then"
    ,   "                    str = str .. \", \""
    ,   "                end"
    ,   "                isInitial = false"
    ,   "                str = str .. key .. \" = \" .. debugToString(value)"
    ,   "            end"
    ,   "            return str .. \"}\""
    ,   "        end"
    ,   "    else"
    ,   "        return tostring(x)"
    ,   "    end"
    ,   "end"
    ,   "function debug(x) print(debugToString(x)) end"
    ]

compileDeclaration :: CoreDeclaration -> Compile Text
compileDeclaration = \case
    CDefineVar name expr -> do
        exprCode <- compileExpr expr
        pure (renderName name <> " = " <> exprCode)

compileExpr :: CoreExpr -> Compile Text
compileExpr = \case
    CVar name -> pure $ renderName name
    CApp funExpr argExpr -> do
        funCode <- compileExpr funExpr
        argCode <- compileExpr argExpr
        pure ("(" <> funCode <> "(" <> argCode <> "))")
    CLambda name body -> do
        bodyCode <- compileExpr body
        pure ("(function (" <> renderName name <> ") return " <> bodyCode <> " end)")
    CCase{} -> undefined
    CLiteral literal -> pure (compileLiteral literal)
    CTupleLiteral arguments -> do
        argumentCodes <- traverse compileExpr arguments
        pure ("({" <> intercalate ", " argumentCodes <> "})")
    -- Wow this is inefficient lol
    CLet name expr rest -> do
        exprCode <- compileExpr expr
        restCode <- compileExpr rest
        pure ("((function (" <> renderName name <> ") return "  <> restCode <> " end)(" <> exprCode <> "))")
    CPrimop primop -> pure (compilePrimop primop)
    -- Types are irrelevant at runtime so this should be fine
    CPi{} -> pure "nil"
    CForall{} -> pure "nil"
    CMeta{} -> undefined
    CTupleType{} -> pure "nil"
    CQuote{} -> undefined

compileLiteral :: Literal -> Text
compileLiteral = \case
    TypeLit -> "nil"
    IntTypeLit -> "nil"
    StringTypeLit -> "nil"
    IntLit n -> show n
    -- TODO: This uses haskell escapes which don't quite match up with lua's
    StringLit string -> show string

compilePrimop :: Primop -> Text
compilePrimop = \case
    Debug -> "debug"

renderName :: Name -> Text
renderName name = Name.original name <> show (hashUnique (Name.unique name))