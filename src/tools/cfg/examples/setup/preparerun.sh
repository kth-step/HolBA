

#https://fredfire1.wordpress.com/2016/06/09/install-and-usage-of-dot-debian-ubuntu-raspberrypi/



sudo apt-get install graphviz
#sudo apt-get install imagemagick


dot test.dot -Tps -o test.ps
xdg-open test.ps

#convert -flatten -density 150 -geometry 100% test.ps test.png

#https://fredfire1.wordpress.com/2016/04/02/install-shellpic-debian-64bit/
#shellpic test.png


