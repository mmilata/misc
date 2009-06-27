module BitString (w8toBs, bsToW8, bsToW8S,
                  bsToW8S', intTo3, b3ToInt,
                  BitString)
where

import Data.Word
import Data.Bits

{-
 - Datovy typ - retezec bitu. True reprezentuje jednicku, False nulu.
 -}
type BitString = [Bool]

{-
 - Prevod Word8 na retezec bitu o delce 8.
 -
 - Definice neni prilis elegantni, nicmene je znatelne rychlejsi nez
 - zakomentovany ekvivalent pod ni.
 -}
w8toBs :: Word8 -> BitString
w8toBs n = [testBit n 7, testBit n 6, testBit n 5, testBit n 4,
            testBit n 3, testBit n 2, testBit n 1, testBit n 0]

{-
w8toBs :: Word8 -> BitString
w8toBs n = map (\x -> testBit n x) [7,6..0]
-}

{-
 - Prevod retezce bitu na Word8.
 -}
bsToW8 :: BitString -> Word8
bsToW8 = snd . foldl (\(n,w) b -> if b then (n-1,setBit w n) else (n-1,w)) (7,0)

{-
 - Prevod retezce bitu na retezec Word8.
 - Pokud neni delka vstupniho retezce nasobkem osmi, je do teto
 - delky doplnen nulami a pocet vyplnovych bitu je vracen jako
 - druha hodnota v usporadane dvojici, kterou tato funkce vraci.
 - Pokud je nasobkem osmi, je druhou polozkou nula.
 -}
bsToW8S :: BitString -> ([Word8],Int)
bsToW8S bs | longerThan7 bs = comb (bsToW8 x) (bsToW8S xs)
           | null bs           = ([], 0)
           | otherwise         = ((bsToW8 $ zeroPad bs):[], 8 - (length bs))
                                 where (x,xs)          = splitAt 8 bs
                                       comb ch (str,n) = (ch:str,n)
                                       zeroPad xs      = xs ++ replicate (8 - (length xs)) False

{-
 - Prevod retezce bitu na retezec Word8.
 - Pokud neni delka vstupniho retezce nasobkem osmi, je vstupni
 - retezec na tuto delku zkracen a zbyla cast je vracena jako druha
 - hodnota v usporadne dvojici, kterou tato funkce vraci.
 -}
bsToW8S' :: BitString -> ([Word8],BitString)
bsToW8S' bs | longerThan7 bs = comb (bsToW8 x) (bsToW8S' xs)
            | null bs           = ([], [])
            | otherwise         = ([], bs)
                                  where (x,xs)            = splitAt 8 bs
                                        comb ch (pre,rem) = (ch:pre,rem)

{-
 - Pomocna fukce zjistujici, zda-li je seznam delsi nez sedm prvku.
 -}
longerThan7 :: [a] -> Bool
longerThan7 (_:_:_:_:_:_:_:_:_) = True
longerThan7 _                   = False

{-
 - Prevod celeho cisla (v rozsahu 0-7) na jeho tribitovou binarni
 - reprezentaci.
 -}
intTo3 :: Int -> [Bool]
intTo3 n = (testBit n 2):(testBit n 1):(testBit n 0):[]

{-
 - Prevod tribitoveho retezce na cele cislo.
 -}
b3ToInt :: (Bool,Bool,Bool) -> Int
b3ToInt (i3,i2,i1) = (if i3 then 4 else 0) +
                     (if i2 then 2 else 0) +
                     (if i1 then 1 else 0)
