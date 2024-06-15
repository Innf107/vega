module Vega.Compile.Lua (compile) where

-- Super simple compilation to lua. This is mostly meant as a sanity check.

import Vega.Prelude
import Vega.Syntax

import Vega.Name qualified as Name

import Data.Vector qualified as Vector
import Vega.Eval
import Vega.Name (freshNameIO)
import qualified Vega.Eval as Eval

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
definitions =
    unlines
        [ "function debugToString(x)"
        , "    if type(x) == \"string\" then"
        , "        return \"\\\"\" .. x .. \"\\\"\""
        , "    elseif type(x) == \"table\" then"
        , "        local arrayLike = true"
        , "        for key, _ in pairs(x) do"
        , "            if type(key) ~= \"number\" then"
        , "                arrayLike = false"
        , "                break"
        , "            end"
        , "        end"
        , "        if arrayLike then"
        , "            local str = \"(\""
        , "            for i, value in ipairs(x) do"
        , "                if (i ~= 1) then"
        , "                    str = str .. \", \""
        , "                end"
        , "                str = str .. debugToString(value)"
        , "            end"
        , "            return str .. \")\""
        , "        else"
        , "            local isInitial = true"
        , "            local str = \"{\""
        , "            for key, value in pairs(x) do"
        , "                if not isInitial then"
        , "                    str = str .. \", \""
        , "                end"
        , "                isInitial = false"
        , "                str = str .. key .. \" = \" .. debugToString(value)"
        , "            end"
        , "            return str .. \"}\""
        , "        end"
        , "    else"
        , "        return tostring(x)"
        , "    end"
        , "end"
        , "function debug(x) print(debugToString(x)) end"
        ]

compileDeclaration :: CoreDeclaration -> Compile Text
compileDeclaration = \case
    CDefineVar name value -> do
        exprCode <- compileValue value
        pure (renderName name <> " = " <> exprCode)
    CDefineGADT _typeName constructors -> do
        let defineConstructor (name, argumentCount) = do
                let result = "{ tag = \"" <> renderName name <> "\"" <> foldMap (\i -> ", x" <> show i) ([1 .. argumentCount] :: Vector Int) <> " }"
                "local " <> renderName name <> " = " <> foldr (\i rest -> "function (x" <> show i <> ") return " <> rest <> " end") result ([1 .. argumentCount] :: Vector Int)
        pure $ intercalate "\n" (fmap defineConstructor constructors)

compileValue :: Eval.Value -> Compile Text
compileValue = \case
    IntV int -> pure $ compileLiteral (IntLit int)
    StringV str -> pure $ compileLiteral (StringLit str)
    Type -> pure "nil"
    Int -> pure "nil"
    String -> pure "nil"
    TupleType{} -> pure "nil"
    _ -> undefined


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
    CCase scrutinee cases -> do
        name <- freshName "x"
        scrutineeCode <- compileExpr scrutinee
        caseCode <- compileCase name cases
        pure
            $ "((function ()\nlocal "
            <> renderName name
            <> " = "
            <> scrutineeCode
            <> "\n"
            <> caseCode
            <> "\n end)())"
    CLiteral literal -> pure (compileLiteral literal)
    CTupleLiteral arguments -> do
        argumentCodes <- traverse compileExpr arguments
        pure ("({" <> intercalate ", " argumentCodes <> "})")
    -- Wow this is inefficient lol
    CLet name expr rest -> do
        exprCode <- compileExpr expr
        restCode <- compileExpr rest
        pure ("((function (" <> renderName name <> ") return " <> restCode <> " end)(" <> exprCode <> "))")
    CPrimop primop -> pure (compilePrimop primop)
    -- Types are irrelevant at runtime so this should be fine
    CPi{} -> pure "nil"
    CForall{} -> pure "nil"
    CMeta{} -> undefined
    CTupleType{} -> pure "nil"
    CQuote{} -> undefined

compileCase :: Name -> (Vector (CorePattern Name, CoreExpr)) -> Compile Text
compileCase scrutinee cases = do
    compiledCases <- traverse go cases
    pure $ "    " <> fold compiledCases <> "\n        error(\"PANIC! non-exhaustive pattern match\")\n    end"
  where
    go (pattern_, expr) = do
        (matchCode, bindCode) <- compileMatch scrutinee pattern_
        exprCode <- compileExpr expr
        pure
            $ "if "
            <> matchCode
            <> " then\n"
            <> bindCode
            <> "        return "
            <> exprCode
            <> "\n"
            <> "    else"
    compileMatch scrutinee = \case
        CWildcardPat -> pure ("true", "")
        CVarPat name -> pure ("true", "        local " <> renderName name <> " = " <> renderName scrutinee <> "\n")
        CIntPat i -> pure (renderName scrutinee <> " == " <> show i, "")
        CStringPat str -> pure (renderName scrutinee <> " == " <> show str, "")
        CTuplePat subPatterns -> do
            let bindings = Vector.imap (\i name -> "        local " <> renderName name <> " = " <> renderName scrutinee <> "[" <> show (i + 1) <> "]") subPatterns
            pure ("true", intercalate "\n" bindings <> "\n")
        CConstructorPat name subPatterns -> do
            let bindings = Vector.imap (\i name -> "        local " <> renderName name <> " = " <> renderName scrutinee <> "[" <> show (i + 1) <> "]") subPatterns
            pure (renderName scrutinee <> ".tag == \"" <> renderName name <> "\"", intercalate "\n" bindings <> "\n")

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
    Add -> "(function (x) return function (y) return x + y end end)"
    Subtract -> "(function (x) return function (y) return x - y end end)"
    Multiply -> "(function (x) return function (y) return x * y end end)"
    IntDivide -> "(function (x) return function (y) return x // y end end)"

renderName :: Name -> Text
renderName name = Name.original name <> show (hashUnique (Name.unique name))
