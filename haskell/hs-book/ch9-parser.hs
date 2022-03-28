-- Chapter 9, A Simpler Parser

import Control.Applicative
import Data.Char

newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }
-- runParser :: Parser a -> String -> Maybe (a, String)

instance Functor Parser where
  -- fmap :: (a -> b) -> Parser a -> Parser b
  fmap f p = Parser $ \str -> case runParser p str of 
                                Just (a, s) -> Just (f a, s)
                                Nothing -> Nothing

instance Applicative Parser where
  pure a = Parser $ \str -> Just(a, str)
  (<*>) fp a = Parser $ \str -> case runParser fp str of
                                  Just (ab, s) -> case runParser a s of
                                                    Just (at, s1) -> Just (ab at, s1)
                                                    Nothing -> Nothing
                                  Nothing -> Nothing

instance Alternative Parser where
  empty = Parser $ \_ -> Nothing
  (<|>) a b = Parser $ \str -> case runParser a str of 
                                 Nothing -> runParser b str
                                 sth -> sth

satisfy :: (Char -> Bool) -> Parser Char
satisfy f = Parser $ \str -> case str of
                               [] -> Nothing
                               s:ss -> if f s then Just (s, ss) else Nothing

char :: Char -> Parser Char
char c = satisfy (== c)

-- some tests
just = runParser (many (satisfy isDigit)) "123abc"
just' = runParser (many (satisfy isDigit)) "abc"
just'' = runParser (some (satisfy isDigit)) "123abc"
just''' = runParser (some (satisfy isDigit)) "abc"
just'''' = (runParser $ char '<' *> many (satisfy isDigit) <* char '>') "<123>"

number :: Parser Int
number = fmap (foldl (\x y -> 10*x+y) 0) (many digit)
  where digit = fmap digitToInt (satisfy isDigit)

sequ :: Parser a -> Parser [a] -> Parser [a]
sequ x y = Parser $ \str -> case runParser x str of
                              Nothing -> Nothing
                              Just (s, ss) -> case runParser y ss of
                                                Nothing -> Nothing
                                                Just(s1, ss1) -> Just(s:s1, ss1)

parseStr :: [Char] -> Parser [Char]
parseStr strs = foldr sequ (Parser $ \str -> Just ("", str)) [char s | s <- strs]

-- some tests
hw = runParser (parseStr "hello") "helloWorld"
