CC = gcc
CXX = g++
CFLAGS ?= -O2 -std=gnu11 -fopenmp
CXXFLAGS ?= -O2 -std=c++17
PYTHON ?= python3
BUILD ?= build
EXAMPLE = examples/n8

ifeq ($(OS),Windows_NT)
EXE = .exe
else
EXE =
endif

.PHONY: all check check-python search
all: $(BUILD)/trailsearch$(EXE) $(BUILD)/literal_check$(EXE)

$(BUILD):
	mkdir -p "$(BUILD)"

$(BUILD)/trailsearch$(EXE): src/trailsearch.c | $(BUILD)
	$(CC) $(CFLAGS) $< -o $@ -lm

$(BUILD)/literal_check$(EXE): src/literal_check.cpp | $(BUILD)
	$(CXX) $(CXXFLAGS) $< -o $@

check: all
	test ! -e "$(BUILD)/reference-replayed.txt"
	test ! -e "$(BUILD)/replayed.txt"
	$(BUILD)/trailsearch$(EXE) $(EXAMPLE)/base.txt $(BUILD)/reference-replayed.txt --plan-in $(EXAMPLE)/reference.plan --time 0 --threads 1
	cmp $(EXAMPLE)/reference.txt $(BUILD)/reference-replayed.txt
	$(BUILD)/trailsearch$(EXE) $(EXAMPLE)/base.txt $(BUILD)/replayed.txt --plan-in $(EXAMPLE)/solution.plan --time 0 --threads 1
	cmp $(EXAMPLE)/solution.txt $(BUILD)/replayed.txt
	$(BUILD)/literal_check$(EXE) 8 01234567 $(BUILD)/replayed.txt --deletions

check-python: | $(BUILD)
	test ! -e "$(BUILD)/python-replayed.txt"
	$(PYTHON) src/applyplan.py $(EXAMPLE)/base.txt $(EXAMPLE)/base.tsv $(EXAMPLE)/solution.plan $(BUILD)/python-replayed.txt
	cmp $(EXAMPLE)/solution.txt $(BUILD)/python-replayed.txt

search: all
	test ! -e "$(BUILD)/search.txt"
	test ! -e "$(BUILD)/search.txt.plan"
	$(BUILD)/trailsearch$(EXE) $(EXAMPLE)/base.txt $(BUILD)/search.txt --plan-in $(EXAMPLE)/reference.plan --time 60 --threads 1 --seed 27003 --kmax 12 --T0 0.7 --ckpt 15 --sync 15
	$(BUILD)/literal_check$(EXE) 8 01234567 $(BUILD)/search.txt
