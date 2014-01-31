# Everything for configuring the make process is done in Make.config

all:
	make -C src depend
	make -C src all

%:
	make -C src $@
