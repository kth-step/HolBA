

main:
	echo "Execute \"Holmake\" in \"src\"."


gendoc:
	cd doc/gen; ./dependencies.py


cleanslate:
	git clean -f -d -x .

