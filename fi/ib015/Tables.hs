module Tables (LookupTable, LookupList, FreqTable,
               hFreqTable, listToTable, tableEncode)
where

import Data.List
import Data.Word
import System.IO
import Data.Array
import Data.Array.IO

import qualified Data.ByteString as B

import BitString

{-
 - Seznam usporadanych dvojic (byte,kodove slove), ktery
 - je pouzity pro vytvoreni kodovaci tabulky.
 -}
type LookupList  = [(Word8,BitString)]

{-
 - Kodovaci tabulka umoznujici zjisteni kodoveho slova
 - pro dany byte v konstantnim case.
 -}
type LookupTable = Array Word8 BitString

{-
 - Seznam usporadanych dvojic (byte,pocet vyskytu v souboru).
 - Pouzita pro vytvoreni kodovaciho stromu.
 -}
type FreqTable   = [(Word8,Int)]

{-
 - Pole bytu a poctu jejich vyskytu pouzite pri prvnim
 - pruchodu vstupnim souborem. Pouzita je implementace
 - IOArray, ktera nevytvari kopii pri kazdem zapise a proto
 - je casove i pametove vyhodna. Pouzita je jeji "unboxed"
 - varianta kvuli vynuceni striktiho vyhodnoceni pri zapisu
 - do ni z duvodu pametove efektivity.
 -}
type FreqArray   = IOUArray Word8 Int

{-
 - Vytvoreni prazdneho pole frekvenci bytu
 -}
emptyFqa :: IO FreqArray
emptyFqa = newArray (0,255) 0

{-
 - Velikost bloku nacitani souboru.
 -}
blockSize :: Int
blockSize = 4096

{-
 - Vytvoreni seznamu frekvenci znaku z handlu souboru. Je
 - vytvoreno prazdne pole, zavolana funkce hFreqTable' a
 - jeji vystup je zbaven znaku s nulovym vyskytem a setriden.
 -}
hFreqTable :: Handle -> IO FreqTable
hFreqTable fh = do hSeek fh AbsoluteSeek 0
                   emptyArr <- emptyFqa
                   unsorted <- hFreqTable' fh emptyArr
                   return $ fqtSort $ filter (\(c,f) -> f /= 0) unsorted

{-
 - Funkce rekurzivne pocitajici vyskyt znaku v souboru.
 - Nacte blok, updatuje tabulku a rekurzivne pokracuje.
 - Pokud dosahne konce soubrou, prevede pole na seznam
 - usporadanych dvojic.
 -}
hFreqTable' :: Handle -> FreqArray -> IO FreqTable
hFreqTable' fh arr = do buf <- B.hGet fh blockSize
                        if B.length buf == 0
                          then
                             getAssocs arr
                          else
                             do updated <- fqaUpdate arr buf
                                hFreqTable' fh updated

{-
 - Update tabulky vyskytu bytu. Prvni parametr je tabulka,
 - druhym je bytestring nacteny ze souboru.
 -}
fqaUpdate :: FreqArray -> B.ByteString -> IO FreqArray
fqaUpdate arr bs | B.null bs = return arr
                 | otherwise = do let w = B.head bs
                                  v <- readArray arr w
                                  writeArray arr w (v+1)
                                  fqaUpdate arr $ B.tail bs

{-
 - Serazeni seznamu usporadanych dvojic sestupne podle poctu
 - vyskytu znaku.
 -}
fqtSort :: FreqTable -> FreqTable
fqtSort fqt = sortBy cmpf fqt
              where cmpf (ca,fa) (cb,fb) | fa == fb  = compare ca cb
                                         | otherwise = compare fa fb

{-
 - Prevede kodovaci seznam na pole.
 -}
listToTable :: LookupList -> LookupTable
listToTable l = array (0,255) l

{-
 - Vyhledani v kodovacim poli.
 -}
tableEncode :: LookupTable -> Word8 -> BitString
tableEncode lut i = lut ! i
