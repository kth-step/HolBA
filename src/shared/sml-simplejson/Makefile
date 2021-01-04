
jsonparse:	jsonparse.mlb json.sml jsonparse.sml
	mlton $<
	./test.sh > test.log 2>&1
	tail -3 test.log

clean:
	rm -f jsonparse test.log


