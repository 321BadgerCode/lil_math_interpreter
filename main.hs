{-# LANGUAGE FlexibleContexts #-}

module Main where

import System.IO (hFlush, stdout)
import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Expr
import qualified Data.Map.Strict as Map
import Control.Monad (void)
import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf)
import Control.Monad.Identity

-- ========================================
-- Data Types
-- ========================================

data Expr
    = Const Double           -- Constant number
    | Var String             -- Variable (e.g., x)
    | Add Expr Expr          -- Addition
    | Sub Expr Expr          -- Subtraction
    | Mul Expr Expr          -- Multiplication
    | Div Expr Expr          -- Division
    | Pow Expr Expr          -- Power (Exponentiation)
    | Sin Expr               -- Sine function
    | Cos Expr               -- Cosine function
    | Tan Expr               -- Tangent function
    | Log Expr Expr          -- Logarithm with base
    | Ln Expr                -- Natural logarithm (base e)
    | Sqrt Expr              -- Square root
    | Abs Expr               -- Absolute value
    deriving (Eq)

instance Show Expr where
    show (Const x)   = show x
    show (Var x)     = x
    show (Add a b)   = "(" ++ show a ++ " + " ++ show b ++ ")"
    show (Sub a b)   = "(" ++ show a ++ " - " ++ show b ++ ")"
    show (Mul a b)   = "(" ++ show a ++ " * " ++ show b ++ ")"
    show (Div a b)   = "(" ++ show a ++ " / " ++ show b ++ ")"
    show (Pow a b)   = "(" ++ show a ++ " ^ " ++ show b ++ ")"
    show (Sin a)     = "sin(" ++ show a ++ ")"
    show (Cos a)     = "cos(" ++ show a ++ ")"
    show (Tan a)     = "tan(" ++ show a ++ ")"
    show (Log a b)   = "log_" ++ show a ++ "(" ++ show b ++ ")"
    show (Ln a)      = "ln(" ++ show a ++ ")"
    show (Sqrt a)    = "sqrt(" ++ show a ++ ")"
    show (Abs a)     = "abs(" ++ show a ++ ")"

-- ========================================
-- Lexer & Parser
-- ========================================

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

symbol :: String -> Parser String
symbol = lexeme . string

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

number :: Parser Expr
number = lexeme $ do
    num <- many1 (digit <|> char '.')
    return $ Const (read num)

variable :: Parser Expr
variable = lexeme $ do
    var <- many1 letter
    return $ Var var

expr :: Parser Expr
expr = buildExpressionParser operators term

operators :: OperatorTable String () Identity Expr
operators = [[Infix (symbol "^" >> return Pow) AssocRight]
             , [Infix (symbol "*" >> return Mul) AssocLeft
               , Infix (symbol "/" >> return Div) AssocLeft]
             , [Infix (symbol "+" >> return Add) AssocLeft
               , Infix (symbol "-" >> return Sub) AssocLeft]
             , [Prefix (symbol "sin" >> return Sin)
               , Prefix (symbol "cos" >> return Cos)
               , Prefix (symbol "tan" >> return Tan)
               ]
             , [Prefix (symbol "sqrt" >> return Sqrt)
               , Prefix (symbol "abs" >> return Abs)
               ]
             , [Prefix (symbol "ln" >> return Ln)]
             ]

term :: Parser Expr
term = parens expr
    <|> number
    <|> variable
    <|> (do
        _ <- symbol "abs"
        x <- parens expr
        return $ Abs x)
            <|> (do
        _ <- symbol "sqrt"
        x <- parens expr
        return $ Sqrt x)
        -- TODO: implement logarithm with base
            <|> (do
        _ <- symbol "ln"
        x <- parens expr
        return $ Log x (Const 2.718281828459045)) -- Natural logarithm (base e)
parseExpr :: String -> Either ParseError Expr
parseExpr input = parse (spaces *> expr <* eof) "" input

-- ========================================
-- Evaluation
-- ========================================

type Env = Map.Map String Double

eval :: Env -> Expr -> Double
eval _ (Const x) = x
eval env (Var x) = fromMaybe (error $ "Undefined variable: " ++ x) (Map.lookup x env)
eval env (Add a b) = eval env a + eval env b
eval env (Sub a b) = eval env a - eval env b
eval env (Mul a b) = eval env a * eval env b
eval env (Div a b) = eval env a / eval env b
eval env (Pow a b) = eval env a ** eval env b
eval env (Sin a) = sin (eval env a)
eval env (Cos a) = cos (eval env a)
eval env (Tan a) = tan (eval env a)
eval env (Log a b) = log (eval env a) / log (eval env b)
eval env (Ln a) = log (eval env a)
eval env (Sqrt a) = sqrt (eval env a)
eval env (Abs a) = abs (eval env a)

-- ========================================
-- Simplification
-- ========================================
-- TODO: the simplification process no longer simplifies constants, so maybe it should. i'ma call it a feature & not a bug tho. 9+10 is way more readable than 21 :D

simplify :: Expr -> Expr
-- Power of a Power rule: (x^a)^b = x^(a * b)
simplify (Pow (Pow (Var "x") a) b) = Pow (Var "x") (Mul a b)

-- Zero exponent rule: x^0 = 1
simplify (Pow _ (Const 0)) = Const 1

-- One exponent rule: x^1 = x
simplify (Pow x (Const 1)) = x

-- Zero multiplication rule: x * 0 = 0
simplify (Mul _ (Const 0)) = Const 0
simplify (Mul (Const 0) _) = Const 0

-- Identity for multiplying by 1: x * 1 = x
simplify (Mul x (Const 1)) = x
simplify (Mul (Const 1) x) = x

-- Multiplying by -1: x * (-1) = -x
simplify (Mul x (Const (-1))) = Sub (Const 0) x
simplify (Mul (Const (-1)) x) = Sub (Const 0) x

-- Division by 1: x / 1 = x
simplify (Div x (Const 1)) = x

-- Combining like terms: x + x = 2x
simplify (Add expr expr') | expr == expr' = Mul (Const 2) expr

-- Simplifying powers: x^a * x^b = x^(a + b)
simplify (Mul (Pow (Var "x") a) (Pow (Var "x") b)) =
    Pow (Var "x") (Add a b)

-- Distributive property: a * (b + c) = a * b + a * c
simplify (Mul a (Add b c)) = Add (Mul a b) (Mul a c)

-- Simplify constant multiplication: 2 * 3 = 6
simplify (Mul (Const a) (Const b)) = Const (a * b)

-- Division simplification: x / x = 1 (when x ≠ 0)
simplify (Div expr expr') | expr == expr' = Const 1

-- Additive identity: x + 0 = x
simplify (Add x (Const 0)) = x
simplify (Add (Const 0) x) = x

-- Additive inverse: x + (-x) = 0
-- TODO: add later

-- Subtraction of zero: x - 0 = x
simplify (Sub x (Const 0)) = x

-- Sine and cosine: sin^2(x) + cos^2(x) = 1
-- TODO: add later

-- Square root of a square: sqrt(x^2) = |x|
simplify (Sqrt (Pow x (Const 2))) = Abs x

-- Logarithmic identity: log_b(x^a) = a * log_b(x)
simplify (Log (Pow x a) b) = Mul a (Log x b)

-- Logarithm of a product: log_b(x * y) = log_b(x) + log_b(y)
simplify (Log (Mul x y) b) = Add (Log x b) (Log y b)

-- Logarithm of a quotient: log_b(x / y) = log_b(x) - log_b(y)
simplify (Log (Div x y) b) = Sub (Log x b) (Log y b)

-- Simplify trigonometric functions (e.g., sin(x), cos(x), tan(x))
simplify (Sin (Const 0)) = Const 0
simplify (Cos (Const 0)) = Const 1
simplify (Tan (Const 0)) = Const 0
simplify (Sin (Const pi)) = Const 0 -- Sin(pi) = 0
simplify (Cos (Const pi)) = Const (-1) -- Cos(pi) = -1

-- Simplify square root expressions (e.g., sqrt(x * x) = |x|)
simplify (Sqrt (Mul expr expr')) | expr == expr' = Abs expr

-- Apply recursive simplification
simplify (Add a b) = Add (simplify a) (simplify b)
simplify (Sub a b) = Sub (simplify a) (simplify b)
simplify (Mul a b) = Mul (simplify a) (simplify b)
simplify (Div a b) = Div (simplify a) (simplify b)
simplify (Pow a b) = Pow (simplify a) (simplify b)
simplify (Sin a) = Sin (simplify a)
simplify (Cos a) = Cos (simplify a)
simplify (Tan a) = Tan (simplify a)
simplify (Log a b) = Log (simplify a) (simplify b)
simplify (Sqrt a) = Sqrt (simplify a)

simplify expr = expr -- Return unchanged if no simplifications apply

-- ========================================
-- REPL
-- ========================================

main :: IO ()
main = do
    putStrLn "'Lil Math Interpreter"
    loop Map.empty
  where
    loop env = do
        putStr ">> "
        hFlush stdout
        line <- getLine
        case line of
            (':':'q':_) -> putStrLn "Goodbye!"
            _ | ":let " `isPrefixOf` line ->
                let rest = drop 5 line
                    (var, exprStr') = break (== '=') rest
                    exprStr = dropWhile (== '=') exprStr'
                    var' = trim var
                 in case parseExpr exprStr of
                        Left err -> print err >> loop env
                        Right ex ->
                            let val = eval env ex
                             in loop (Map.insert var' val env)
              | ":eval " `isPrefixOf` line ->
                let exprStr = drop 6 line
                 in case parseExpr exprStr of
                        Left err -> print err >> loop env
                        Right ex -> do
                            print $ eval env ex
                            loop env
              | ":simp " `isPrefixOf` line ->
                let exprStr = drop 6 line
                 in case parseExpr exprStr of
                        Left err -> print err >> loop env
                        Right ex -> do
                            print $ simplify ex
                            loop env
              | ":h" `isPrefixOf` line -> do
                putStrLn "Available commands:\n:let <var> = <expr>  -- Define a variable\n:eval <expr>      -- Evaluate an expression\n:simp <expr>      -- Simplify an expression\n:q                -- Quit the interpreter\n:h                -- Help"
                loop env
              | otherwise -> do
                  case parseExpr line of
                      Left err -> print err
                      Right ex -> print ex
                  loop env

    trim = f . f
        where f = reverse . dropWhile (== ' ')