module Navi.Error (Error (..)) where

import Navi.Prelude

import Navi.Loc qualified as Loc
import Navi.Pretty qualified as Pretty

import Navi.Lexer qualified as Lexer
import Navi.Parser qualified as Parser
import Navi.Types qualified as Types

data Error
    = LexError Lexer.LexError
    | ParseError Parser.ParseError
    | TypeError Types.TypeError

prettyLoc :: (?style :: style, Pretty.TextStyle style) => Loc.Loc -> Pretty.Doc style
prettyLoc loc = 
    Pretty.emphasis (show loc) 
        <> Pretty.literal ": " 
        <> Pretty.error "ERROR:"
        <> Pretty.literal "\n"

instance Pretty.Pretty Error where
    pretty (LexError err) = case err of
        Lexer.UnexpectedChar char ->
            Pretty.literal "Unexpected character: "
                <> Pretty.identifier (show char)
        Lexer.UnexpectedEOF ->
            Pretty.literal "Unexpected end of file"
    pretty (ParseError err) = case err of
        Parser.ParseError tokens ->
            Pretty.literal "Parse error\n"
                <> Pretty.literal
                    ( "  next tokens: "
                        <> show (map (\(Lexer.Token tokenClass _) -> tokenClass) $ take 10 tokens)
                    )
        Parser.UnexpectedEOF -> Pretty.literal "Unexpected end of file"
        Parser.MismatchedDeclName loc sigName defName ->
            prettyLoc loc
                <> Pretty.literal "Mismatched variable name in definition.\n"
                <> Pretty.literal "    The type signature defines a variable named " <> Pretty.identifier sigName <> Pretty.literal "\n"
                <> Pretty.literal "             But its definition refers to it as " <> Pretty.identifier defName
    pretty (TypeError err) = case err of
        Types.UnableToUnify loc actual expected (fullActual, fullExpected) ->
            prettyLoc loc
                <> Pretty.literal "Unable to unify\n"
                <> Pretty.literal "       expected type "
                <> Pretty.pretty expected
                <> Pretty.literal "\n"
                <> Pretty.literal "    with actual type "
                <> Pretty.pretty actual
                <> Pretty.literal "\n"
                <> Pretty.literal "While trying to unify\n"
                <> Pretty.literal "       expected type "
                <> Pretty.pretty fullExpected
                <> Pretty.literal "\n"
                <> Pretty.literal "    with actual type "
                <> Pretty.pretty fullActual
        Types.ApplicationOfNonPi loc value ->
            prettyLoc loc
                <> Pretty.literal "Application of non-pi value: " <> Pretty.pretty value
        Types.UnableToInferLambda loc ->
            prettyLoc loc
                <> Pretty.literal "Unable to infer type of lambda expression.\n"
                <> Pretty.literal "  Please provide an explicit type signature"
        Types.DefiningLambdaAsNonPi loc ty ->
            prettyLoc loc
                <> Pretty.literal "Lambda expression is expected to have non-function type " <> Pretty.pretty ty
        Types.MoreArgumentsThanInType loc number ->
            prettyLoc loc 
                <> Pretty.literal "Function definition is defined with too many arguments.\n"
                <> Pretty.literal "It has "
                <> Pretty.number number
                <> Pretty.literal " more than its type suggests"
