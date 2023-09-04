# MLLab6/HOL/HOLReports/Holmakefile

INCLUDES = ../

# build

all: build_HOL build_Report

build_HOL:
	@cd HOL && Holmake

build_Report:
	@cd Report && make


# clean

clean:
	@cd HOL && Holmake clean
	@cd Report && make clean


# clean and rebuild

rebuild: clean all

