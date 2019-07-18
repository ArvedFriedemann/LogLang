module YATRS where

import Control.Monad
import Text.Parsec hiding (spaces)

data Term a = BOT | ATOM a | VAR a | APPL (Term a) (Term a) deriving (Eq, Show)
data Equation a = EQTERM (Term a) | IMPL (Equation a) (Equation a) deriving (Eq, Show)

spaces::Parsec String st String
spaces = many $ oneOf "\t\n "

spaces1::Parsec String st String
spaces1 = many1 $ oneOf "\t\n "

termEnd::Parsec String st ()
termEnd = lookAhead $ (void $ oneOf ")\n") <|> eof

embrace::Parsec String st a -> Parsec String st b -> Parsec String st c -> Parsec String st b
embrace b p b' = do {b; r<-p; b'; return r}

symbol::Parsec String st a -> Parsec String st a
symbol p = embrace (many $ oneOf "\t ") p (many $ oneOf "\t ")

followedBy::Parsec String st b -> Parsec String st c -> Parsec String st b
followedBy p b = do {r<-p; b; return r}

parseIdfrName::Parsec String st String
parseIdfrName = manyTill (noneOf "\t\n ()") (try $ string "->")

parseVar::Parsec String st (Term String)
parseVar = do {
  n <- upper <|> (char '_');
  name <- parseIdfrName;
  return $ VAR $ n:name
}

parseAtom::Parsec String st (Term String)
parseAtom = do {
  name <- parseIdfrName;
  return $ ATOM $ name
}

parseIdfr::Parsec String st (Term String)
parseIdfr = (try parseVar) <|> (try parseAtom) <|> (try (string "()" >> (return BOT)))

parseTerms::Parsec String st [Term String]
parseTerms = manyTill ((try $ embrace (char '(') parseTerm (char ')' >> spaces) )<|>(symbol parseIdfr)) (try termEnd);

parseTerm::Parsec String st (Term String)
parseTerm = leftAssocTerm <$> (parseTerms `followedBy` spaces)

leftAssocTerm::[Term a] -> Term a
leftAssocTerm [] = BOT
leftAssocTerm lst = foldl1 APPL lst

--parseEquation:: Parsec String st (Equation String)
--parseEquation = parseTerm `sepBy1` (string "->")
