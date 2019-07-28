module YATRSParser where

import Control.Monad
import Text.Parsec hiding (spaces)
import Data.Either
import YATRS
--import YATRS2

impsymb = "->"
impOp = ATOM impsymb
botsymb = "()"

spaces::Parsec String st String
spaces = many $ oneOf "\t\n "

spaces1::Parsec String st String
spaces1 = many1 $ oneOf "\t\n "

inlineSpaces::Parsec String st String
inlineSpaces = many $ oneOf "\t "

inlineSpaces1::Parsec String st String
inlineSpaces1 = many1 $ oneOf "\t "

termEnd::Parsec String st ()
termEnd = lookAhead $ (void $ oneOf ")\n") <|> eof

embrace::Parsec String st a -> Parsec String st b -> Parsec String st c -> Parsec String st b
embrace b p b' = do {b; r<-p; b'; return r}

parens::Parsec String st a -> Parsec String st a
parens p = embrace (char '(' >> inlineSpaces) p (inlineSpaces >> char ')')

symbol::Parsec String st a -> Parsec String st a
symbol p = embrace (many $ oneOf "\t ") p (many $ oneOf "\t ")

followedBy::Parsec String st b -> Parsec String st c -> Parsec String st b
followedBy p b = do {r<-p; b; return r}

parseIdfrName::Parsec String st String
parseIdfrName = manyTill anyChar $ lookAhead $ choice $ try <$> [void $ string impsymb, void $ string ".", void $ oneOf "\t\n ()", void $ eof]

parseVar::Parsec String st (Term String)
parseVar = do {
  n <- upper <|> (char '_');
  name <- parseIdfrName;
  return $ VAR $ n:name
}

parseAtom::Parsec String st (Term String)
parseAtom = do {
  char '`';
  name <- manyTill anyChar (char '`');
  return $ ATOM name
} <|> do {
  name <- parseIdfrName;
  case name of
    [] -> fail ""
    _ -> return $ ATOM name
}

parseIdfr::Parsec String st (Term String)
parseIdfr = (try parseVar) <|> (try parseAtom) <|> (try (string botsymb >> (return BOT)))

parseTerminal::Parsec String st (Term String)
parseTerminal = parens parseImpl <|> parseIdfr

parseTerm::Parsec String st (Term String)
parseTerm = parseTerminal `chainl1` ((try $ (inlineSpaces1 >> (lookAhead $ try $ parseTerminal)) ) >> (return APPL))

parseImpl::Parsec String st (Term String)
parseImpl = parseTerm `chainl1` ((symbol $ string impsymb) >> return (\x y -> APPL (APPL (ATOM impsymb) x) y) )

parseKB::Parsec String st [Term String]
parseKB = parseImpl `sepEndBy` (symbol (string "." <|> string "\n") )


termToString::Term String -> String
termToString BOT = botsymb
termToString (ATOM x) = case parse parseAtom "" x of
                          Right _ -> x
                          Left  _ -> "`"++x++"`"
termToString (VAR x)  = case parse parseVar "" x of
                          Right _ -> x
                          Left  _ -> '_':x
termToString a@(APPL (APPL (ATOM op) x) y)
  | op==impsymb = (termToString x)++" "++impsymb++" "++(termToString y)
  | otherwise = termToString' a
termToString x = termToString' x

termToString'::Term String -> String
termToString' (APPL x b@(APPL y z)) = (termToString x)++" ("++(termToString b)++")"
termToString' (APPL x y) = (termToString x)++" "++(termToString y)
termToString' x = termToString x

termFromString::String -> Term String
termFromString s = case parse parseImpl "" s of
                      Right t -> t
                      Left err -> error (show err)
ts = termFromString

kbFromString::String -> KB String
kbFromString s = case parse parseKB "" s of
                      Right t -> t
                      Left err -> error (show err)
kbs = kbFromString

formatTerms::[Term String] -> String
formatTerms terms = unlines $ termToString <$> terms

outputTerms::[Term String] -> IO ()
outputTerms terms = putStrLn $ formatTerms terms

fromRight::b -> Either a b -> b
fromRight _ (Right x)= x
fromRight d _ = d
