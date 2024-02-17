{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

import qualified Data.ByteString as BS
import Data.List
import Foreign.C.String
import Foreign.Ptr
import Foreign.Storable
import Numeric
import Data.Word
import Data.Bits
import Data.Char
import Data.Proxy
import Data.Maybe
import Text.Parsec hiding (State)
import Data.List.Split (chunksOf)
-- import Text.Parsec.ByteString


foreign import ccall "syscall" syscall0 :: Int -> IO Int
foreign import ccall "syscall" syscall1 :: Int -> Int -> IO Int
foreign import ccall "syscall" syscall2 :: Int -> Int -> Int -> IO Int
foreign import ccall "syscall" syscall3 :: Int -> Int -> Int -> Int -> IO Int
foreign import ccall "syscall" syscall4
  :: Int -> Int -> Int -> Int -> Int -> IO Int
foreign import ccall "syscall" syscall5
  :: Int -> Int -> Int -> Int -> Int -> Int -> IO Int
foreign import ccall "syscall" syscall6
  :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> IO Int

data LHSToken = LWildcard | LBit Bool
  deriving (Show)
data RHSToken = RRef Int | RBit Bool
  deriving (Show)
data Transition = Transition [LHSToken] [RHSToken]
  deriving (Show)
type Program = [Transition]
type State = [Bool]

matchesState :: State -> [LHSToken] -> Bool
matchesState s l = bitsMatch s l
  where
    bitsMatch [] [] = True
    bitsMatch _ [] = True
    bitsMatch [] _ = False
    bitsMatch (_:st) (LWildcard:lhs) = bitsMatch st lhs
    bitsMatch (b1:st) (LBit b2:lhs) = b1 == b2 && bitsMatch st lhs

iter :: Program -> State -> Either String State
iter p s = case find (matchesState s . (\(Transition l _) -> l)) p of
  Nothing -> Left "No matching pattern found"
  Just (Transition l r) -> do
    transitioned <- mapM transition r
    pure $ transitioned ++ drop (length l) s
  where
    transition (RBit b) = Right b
    transition (RRef n)
      | length s > n = Right $ s !! n
      | otherwise =
        Left $ "The referenced index " ++ show n
           ++ " is out of state bounds for state of length " ++ show (length s)

iterIO :: Program -> State -> IO (Either String State)
iterIO p s
  | take 24 s == strBits "req" =
    case bitsToChar (take 8 $ drop 24 s) of
      'r' -> do
        w8 <- peek (ptrAt 32) :: IO Word8
        pure $ Right $ strBits "repr" ++ fbToBits w8 ++ drop (32 + 8) s
      'w' -> do
        poke (ptrAt 32) (fbAt (Proxy :: Proxy Word8) (32 + intSz))
        pure $ Right $ strBits "repw" ++ drop 32 s
      c -> if c >= '0' && c <= '6'
           then do
        r <- case c of
          '0' -> syscall0 (intAt 32)
          '1' -> syscall1 (intAt 32) (intAt (32 + intSz))
          '2' -> syscall2 (intAt 32) (intAt (32 + intSz)) (intAt (32 + intSz * 2))
          '3' -> syscall3 (intAt 32) (intAt (32 + intSz)) (intAt (32 + intSz * 2))
            (intAt (32 + intSz * 3))
          '4' -> syscall4 (intAt 32) (intAt (32 + intSz)) (intAt (32 + intSz * 2))
            (intAt (32 + intSz * 3)) (intAt (32 + intSz * 4))
          '5' -> syscall5 (intAt 32) (intAt (32 + intSz)) (intAt (32 + intSz * 2))
            (intAt (32 + intSz * 3)) (intAt (32 + intSz * 4))
            (intAt (32 + intSz * 5))
          '6' -> syscall6 (intAt 32) (intAt (32 + intSz)) (intAt (32 + intSz * 2))
            (intAt (32 + intSz * 3)) (intAt (32 + intSz * 4))
            (intAt (32 + intSz * 5)) (intAt (32 + intSz * 6))
        pure $ Right $ strBits ("rep" ++ [c]) ++ fbToBits r ++ drop (32 + intSz) s
           else pure $ Left $ "An unknown sys command: " ++ [c]
  | otherwise = pure $ iter p s
  where
    intSz = finiteBitSize (0 :: Int)
    fbAt :: FiniteBits a => Proxy a -> Int -> a
    fbAt (Proxy :: Proxy a) offset =
      bitsToFB (take (finiteBitSize (zeroBits :: a)) (drop offset s))
    intAt :: Int -> Int
    intAt = fbAt (Proxy :: Proxy Int)
    ptrAt offset = wordPtrToPtr (WordPtr (fbAt (Proxy :: Proxy Word) offset))

run :: Program -> State -> IO (Either String State)
run p s = do
  let asBinary True = '1'
      asBinary False = '0'
  -- putStrLn $ map asBinary s
  -- putStrLn $ map bitsToChar $ chunksOf 8 s
  r <- iterIO p s
  case r of
    Left err -> pure $ Left err
    Right s' -> run p s'

main :: IO ()
main = do
  c <- BS.getContents
  case runParser pProgram () "input" c of
    Right p -> do
      -- print p
      print =<< run p (strBits "start")
    Left err -> print err

fbToBits :: FiniteBits a => a -> [Bool]
fbToBits bits = let sz = finiteBitSize bits in
            [ testBit bits (sz - n) | n <- [1..sz] ]

bitsToFB :: FiniteBits a => [Bool] -> a
bitsToFB [] = zeroBits
bitsToFB (True:xs) = setBit (bitsToFB xs) (length xs)
bitsToFB (False:xs) = bitsToFB xs

charToBits :: Char -> [Bool]
charToBits c
  | ord c < 128 = fbToBits (fromIntegral (ord c) :: Word8)

bitsToChar :: [Bool] -> Char
bitsToChar b = chr $ fromIntegral (bitsToFB b :: Word8)

bsBits :: BS.ByteString -> [Bool]
bsBits = concatMap fbToBits . BS.unpack

strBits :: String -> [Bool]
strBits = concatMap charToBits

-- data ParserState = PS { lhsBits :: Int
--                       , rhsBits :: Int
--                       } deriving (Show, Eq)

type Parser = Parsec BS.ByteString ()

pHex :: Parser (Integer, Int)
pHex = do
  char 'x'
  digits <- many1 hexDigit
  let bitNum = length digits * 4
      [(n, "")] = readHex digits
  pure (n, bitNum)

pBin :: Parser (Integer, Int)
pBin = do
  digits <- many1 (oneOf ['0', '1'])
  let bitNum = length digits
      [(n, "")] =
        readInt 2 (`elem` ("01" :: String)) (\x -> ord x - 0x30) digits
  pure (n, bitNum)

pChars :: Parser [Bool]
pChars = do
  char '\''
  c <- anyChar
  cs <- many (noneOf " \n")
  pure $ concatMap charToBits (c:cs)

pNum :: Parser (Integer, Int)
pNum = choice [pHex, pBin]

pNum' :: Parser Integer
pNum' = fst <$> pNum

pNumBits :: Parser [Bool]
pNumBits = do
  (n, nBits) <- pNum
  pure $ map (\pos -> testBit n (nBits - pos)) [1..nBits]

pWildcard :: Parser [LHSToken]
pWildcard = char '_' *>
            (((\n -> replicate (fromIntegral n) LWildcard) <$> pNum')
              <|> pure [LWildcard])

pLHS :: Parser [LHSToken]
pLHS = choice
  [ map LBit <$> pNumBits
  , map LBit <$> pChars
  , pWildcard
  ]

pRef :: Parser [RHSToken]
pRef = do
  char '^'
  from <- pNum'
  len <- option 0 (char '+' *> pNum')
  pure $ map (RRef . fromInteger) [from..from + len]

pRHS :: Parser [RHSToken]
pRHS = choice
  [ map RBit <$> pNumBits
  , map RBit <$> pChars
  , pRef
  ]

pTransition :: Parser Transition
pTransition = do
  lhs <- concat <$> (pLHS `sepEndBy` char ' ') <?> "LHS"
  string ". "
  rhs <- concat <$> (pRHS `sepBy` char ' ') <?> "RHS"
  pure $ Transition lhs rhs

pComment :: Parser String
pComment = char '#' *> many (noneOf "\n")

pProgramLine :: Parser (Maybe Transition)
pProgramLine = (pComment *> pure Nothing)
               <|> (pure <$> pTransition)

pProgram :: Parser Program
pProgram =
  catMaybes <$> (pProgramLine <?> "transition") `sepEndBy1` (many1 newline)
  <* eof
