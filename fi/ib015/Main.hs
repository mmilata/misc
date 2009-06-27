module Main (main) where

import System.Environment
import System.IO
import System.Directory

import qualified Data.ByteString as B

import Htree
import Tables
import BitString

{-
 - Hlavni funkce. Zjisti, zda-li je programu predan spravny pocet
 - spravnych argumentu a podle toho bud provede kodovani/dekodovani
 - nebo vypise napovedu.
 -}
main :: IO ()
main = do args <- getArgs
          if length args /= 2
             then
                printUsage
             else
                case (head args) of
                   "-c" -> doEncode (args !! 1)
                   "-d" -> doDecode (args !! 1)
                   _    -> printUsage


{-
 - Funkce vypisujici napovedu k programu.
 -}
printUsage :: IO ()
printUsage = hPutStrLn stderr ("Usage: huffman [-c|-d] FILE\n\n" ++
                               " -c\tEncode FILE\n"              ++
                               " -d\tDecode FILE\n\n"            ++
                               "2007, Martin Milata, <256615@mail.muni.cz>")

{-
 - Provedeni kodovani. Funkce zjisti, jestli jiz neexistuje
 - soubor, ktery ma stejne jmeno jako by bylo jmeno vystupniho souboru
 - a pokud ano, skonci s chybou. Jinak otevre vstupni soubor, v prvnim
 - pruchodu z nej sestavi tabulku vyskytu znaku a z ni kodovaci strom,
 - pak otevre vystupni soubor a zavola funkci provadejici kodovani. Te
 - je navic predan retezec tri bitu, ktere vyplni zacatek souboru a
 - ktere pak budou prepsany trojici bitu znacici kolik bitu je pouzito
 - pro vyplneni konce souboru a dale bitova reprezentace kodovaciho
 - stromu.
 -}
doEncode :: FilePath -> IO ()
doEncode s = do fileExists <- doesFileExist outfile
                if fileExists
                   then
                      hPutStrLn stderr "Output file already exists -- exitting"
                   else do
                      rh <- openFile s ReadMode
                      hSetBinaryMode rh True
                      fqt <- hFreqTable rh
                      let htree = (buildTree fqt)

                      rh <- openFile s ReadMode
                      hSetBinaryMode rh True
                      wh <- openFile outfile ReadWriteMode
                      hSetBinaryMode wh True
                      hSeek rh AbsoluteSeek 0
                      fill <- fhEncode rh wh (lookupTable htree) ([False, False, False] ++ serializeHtree htree)
                      updateFirstByte wh fill
                      hClose rh
                      hClose wh
             where
                outfile = s ++ ".huf"


{-
 - Provedeni dekodovani. Funkce zjisti, zda-li ma vstupni soubor koncovku
 - .huf a zda-li jiz neexistuje soubor bez ni, ktery je pouzit jako vystupni.
 - Nejdrive je nactena hlavicka souboru, z ktere je sestaven kodovaci strom
 - a pocte bitu, ktere se maji na konci souboru ignorovat. Pote je zavolana
 - funkce provadejici samotne dekodovani.
 -}
doDecode :: FilePath -> IO ()
doDecode s = if suffix /= ".huf"
                then
                   hPutStrLn stderr "Suffix not .huf -- exitting"
                else do
                   fileExists <- doesFileExist basename
                   if fileExists
                      then
                         hPutStrLn stderr "Output file already exists -- exitting"
                      else do
                         rh <- openFile s ReadMode
                         wh <- openFile basename WriteMode
                         hSetBinaryMode rh True
                         hSetBinaryMode wh True
                         (fill,tree,rest) <- fhDecodeTree rh
                         fhDecode rh wh tree rest fill
                         hClose rh
                         hClose wh
             where
                (basename,suffix) = splitAt ((length s)-4) s

{-
 - Zapsani poctu "vyplnovych" bitu do prvnich tri bitu prvniho bitu.
 -}
updateFirstByte :: Handle -> Int -> IO ()
updateFirstByte wh n = do hSeek wh AbsoluteSeek 0
                          b <- B.hGet wh 1
                          let (_:_:_:bits) = w8toBs $ B.head b
                          hSeek wh AbsoluteSeek 0
                          B.hPut wh $ B.singleton $ bsToW8 (intTo3 n ++ bits)
