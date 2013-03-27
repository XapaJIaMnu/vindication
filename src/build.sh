rm -rf *.hi
rm -rf *.o
rm -rf main
ghc --make main.hs
mv main carneades
rm -rf *.hi
rm -rf *.o
