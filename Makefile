all: parser
	ghc -prof -auto-all -caf-all --make Main.hs -o interpreter

parser:
	bnfc Haskall.cf
	happy -gca ParHaskall.y
	alex -g LexHaskall.x
    

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocHaskall.ps
distclean: clean
	-rm -f DocHaskall.* LexHaskall.* ParHaskall.* LayoutHaskall.* SkelHaskall.* PrintHaskall.* TestHaskall.* AbsHaskall.* TestHaskall ErrM.* SharedString.* Haskall.dtd XMLHaskall.* *.bak

