module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces)

data Term a = BOT | ATOM a | VAR a | APPL (Term a) (Term a) deriving (Eq, Show)

impsymb = "->"

spaces::Parsec String st String
spaces = many $ oneOf "\t\n "

spaces1::Parsec String st String
spaces1 = many1 $ oneOf "\t\n "

inlineSpaces::Parsec String st String
inlineSpaces = many1 $ oneOf "\t "

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
  name <- parseIdfrName;
  case name of
    [] -> fail ""
    _ -> return $ ATOM $ name
}

parseIdfr::Parsec String st (Term String)
parseIdfr = (try parseVar) <|> (try parseAtom) <|> (try (string "()" >> (return BOT)))

parseTerminal::Parsec String st (Term String)
parseTerminal = parens parseTerm <|> parseIdfr

parseTerm::Parsec String st (Term String)
parseTerm = parseTerminal `chainl1` ((try $ (inlineSpaces1 >> (lookAhead $ try $ parseTerminal)) ) >> (return APPL))

parseImpl::Parsec String st (Term String)
parseImpl = parseTerm `chainl1` ((symbol $ string impsymb) >> return (\x y -> APPL (APPL (VAR impsymb) x) y) )

parseKB::Parsec String st [Term String]
parseKB = parseImpl `sepEndBy` (symbol (string "." <|> string "\n") )
