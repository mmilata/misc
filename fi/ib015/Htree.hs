module Htree (buildTree, fhEncode, fhDecode, fhDecodeTree,
              lookupTable, serializeHtree, unserializeHtree,
              Htree)
where

import Data.Word
import Data.List
import System.IO

import qualified Data.ByteString as B

import BitString
import Tables

{-
 - Datovy typ binarniho kodovaciho stromu.
 - List obsahuje byte, ktery reprezentuje a cele cislo pouzite
 - v pripade, ze se strom sestavuje z tabulek frekvenci.
 - Uzel stromu pak obsahuje dva listy a celociselnou hodnotu
 - reprezentujici frekvenci vsech listu tohoto podstromu.
 -}
data Htree = Hleaf Int Word8 | Hnode Int Htree Htree
     deriving Show

{-
 - Pristupova funkce pro zjisteni frekvence (pod)stromu.
 -}
freq :: Htree -> Int
freq (Hleaf n _)   = n
freq (Hnode n _ _) = n

{-
 - Vytvoreni listu stromu z usporadane dvojice obsahujici
 - byte a pocet jeho vyskytu v souboru.
 -}
mkleaf :: (Word8,Int) -> Htree
mkleaf (x,n) = Hleaf n x

{-
 - Vytvoreni kodovaciho stromu ze setrideneho seznamu bytu vyskytujicich
 - se v kodovanem soubrou a poctu jejich vyskytu.
 -}
buildTree :: FreqTable -> Htree
buildTree = unarray . until ((==1) . length) jointree . map mkleaf
            where jointree (a:b:xs) = insertBy cmpf (mergeTree a b) xs
                  cmpf a b          = compare (freq a) (freq b)
                  unarray (a:[])    = a

{-
 - Spojeni dvou stromu. Je vytvoren novy uzel, argumenty se stanou jeho
 - potomky.
 -}
mergeTree :: Htree -> Htree -> Htree
mergeTree a b = Hnode (freq a + freq b) a b

{-
 - Vytvoreni vyhledavaci tabulky z kodovaciho stromu. Pro zakodovani bytu
 - tak nemusime prochazet cely strom, sekvenci bitu odpovidajicich kodovanemu
 - bytu zjistime z tabulky v konstanim case.
 -}
lookupTable :: Htree -> LookupTable
lookupTable = listToTable . treeToList

{-
 - Prevod kodovaciho stromu na seznam usporadanych dvojic
 - (byte,retezec bitu), ktery bude pouzit pro vytvoreni vyhledavaci
 - tabulky.
 -}
treeToList :: Htree -> LookupList
treeToList (Hleaf _ c)   = [(c,[])]
treeToList (Hnode _ a b) = (prepend False (treeToList a)) ++ (prepend True (treeToList b))
                            where prepend b = map (\(c,bs) -> (c,b:bs))

{-
 - Zakodovani bytu podle vyhledavaci tabulky
 -}
encCh :: LookupTable -> Word8 -> BitString
encCh = tableEncode

{-
 - Dekodovani retezce bitu na byte. Je vracena usporadana dvojice
 - bytu a zbyvajicich bitu, ktere jsou zacatkem dalsiho znaku.
 - Pokud se takova sekvence bitu nenachazi v kodovacim strome,
 - zrejme jsme nacetli ze souboru jen cast kodovaciho slova,
 - takze vratime Nothing a precteme dalsi blok souboru.
 -}
decCh :: Htree -> BitString -> Maybe (Word8,BitString)
decCh (Hleaf _ c) bs       = Just (c,bs)
decCh (Hnode _ l r) []     = Nothing
decCh (Hnode _ l r) (b:bs) = decCh child bs
                             where child = if b then r else l

{-
 - Dekodovani retezce bitu na retezec odpovidajicich bytu a
 - konce retezce, ktery nelze dekodovat, protoze nereprezentuje
 - cele kodove slovo.
 -}
decChs :: Htree -> BitString -> ([Word8],BitString)
decChs tree bs = case decCh tree bs of
                   Just (c,rest) -> let (cs,rest') = decChs tree rest in (c:cs,rest')
                   Nothing       -> ([],bs)

{-
 - Prevod kodovaciho stromu na retezec bitu. Algoritmus
 - je popsan v dokumentaci.
 -}
serializeHtree :: Htree -> BitString
serializeHtree (Hleaf _ c)   = True : w8toBs c
serializeHtree (Hnode _ a b) = [False] ++ serializeHtree a ++ [False] ++ serializeHtree b ++ [True]

{-
 - Prevod retezce bitu na kodovaci strom a zbytek bitu, ktere
 - se nachazi za timto stromem.
 -}
unserializeHtree :: BitString -> (Htree,BitString)
unserializeHtree (True:xs)  = (Hleaf 0 (bsToW8 byte), rest)
                              where (byte, rest) = splitAt 8 xs
unserializeHtree (False:xs) = (Hnode 0 l r, tail rrest)
                              where (l, lrest) = unserializeHtree xs
                                    (r, rrest) = unserializeHtree (tail lrest)

{-
 - Velikost bufferu pro cteni.
 -}
rBufSize :: Int
rBufSize = 4096

{-
 - Rekurzivni kodovani souboru po blocich. Prvni argument je handle
 - vstupniho souboru, druhy handle vystupniho souboru, treti vyhledavaci
 - tabulka pouzita ke kodovani, ctvrty retezec bitu ktery zbyl z predchozi
 - iterace, je kratsi nez 8 a tudiz se z nej neda vytvorit byte. Vracen
 - je pocet bitu, ktere bylo nutno pouzit na doplneni posledniho bytu,
 - kdyz je dosazen konec vstupniho souboru.
 -}
fhEncode :: Handle -> Handle -> LookupTable -> BitString -> IO Int
fhEncode rh wh lut pre = do buf <- B.hGet rh rBufSize
                            if B.length buf == 0
                              then
                                do let (str,rem) = bsToW8S pre
                                   B.hPut wh $ B.pack str
                                   return rem
                              else
                                do let (out,newpre) = bsToW8S' $ (pre++) $ B.foldr (\x done -> (encCh lut x) ++ done) [] buf
                                   B.hPut wh $ B.pack out
                                   fhEncode rh wh lut newpre

{-
 - Dekodovani hlavicky vstupniho souboru, ktera obsahuje kolik bitu na
 - konci souboru je pouzito pro vyplneni, kodovaci strom a dale cast
 - retezce bitu samotnych dat, ktere byly nacteny v bloku spolecne s
 - hlavickou.
 -}
fhDecodeTree :: Handle -> IO (Int,Htree,BitString)
fhDecodeTree rh = do buf <- B.hGet rh rBufSize
                     let (i3:i2:i1:bits) = B.foldr (\x done -> w8toBs x ++ done) [] buf
                     let (tree,rest) = unserializeHtree bits
                     return (b3ToInt(i3,i2,i1),tree,rest)

{-
 - Rekurzivni dekodovani souboru po blocich. Prvni argument je handle
 - vstupniho souboru, druhy handle vystupniho souboru, treti je
 - kodovaci strom pouzity k dekodovani, ctvrty retezec bitu z predchozi
 - iterace, ktery netvori cele kodovaci slovo, paty pocet bitu, ktere
 - jsou pouzity jako vypln na konci souboru.
 -}
fhDecode :: Handle -> Handle -> Htree -> BitString -> Int -> IO ()
fhDecode rh wh tree pre fill = do buf <- B.hGet rh rBufSize
                                  if B.length buf == 0 && length pre == fill
                                    then
                                      return ()
                                    else
                                      do let (bits,end) = cutEnd fill $ pre ++ B.foldr (\x done -> w8toBs x ++ done) [] buf
                                         let (out,rest) = decChs tree bits
                                         B.hPut wh $ B.pack out
                                         fhDecode rh wh tree (rest++end) fill
                               where cutEnd n xs = splitAt ((length xs)-n) xs
