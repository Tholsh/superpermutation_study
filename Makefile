# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Theo H.
# The search includes its library sources; compile its entry point once.
.DEFAULT_GOAL := all
CXX ?= g++
CPPFLAGS ?=
CXXFLAGS ?= -O3 -std=c++17
PAINT_CXXFLAGS ?= -O3 -std=c++20
LDFLAGS ?=
LDLIBS ?=
BUILD_DIR := build
LIB_DIR := boundary-spectral-n11-20261004

ifeq ($(OS),Windows_NT)
SHELL := cmd.exe
.SHELLFLAGS := /c
EXE := .exe
else
EXE :=
endif

SEARCH_SOURCES := search/course_exchange.cpp \
    $(LIB_DIR)/coupled_cycle_search.cpp $(LIB_DIR)/phase_cut_spectral.cpp \
    $(LIB_DIR)/boundary_transfer.cpp $(LIB_DIR)/construct.cpp
CHECKER_NAMES := literal_check verify_standalone verify_sorted
CHECKER_BINARIES := $(addprefix $(BUILD_DIR)/,$(addsuffix $(EXE),$(CHECKER_NAMES)))
BINARIES := $(BUILD_DIR)/course_exchange$(EXE) $(CHECKER_BINARIES) $(BUILD_DIR)/paint-waste$(EXE) $(BUILD_DIR)/boundary_transfer$(EXE)
DEPFILES := $(addsuffix .d,$(basename $(BINARIES)))

.PHONY: all course_exchange checkers paint-waste boundary_transfer clean
all: course_exchange
course_exchange: $(BUILD_DIR)/course_exchange$(EXE)
checkers: $(CHECKER_BINARIES)
paint-waste: $(BUILD_DIR)/paint-waste$(EXE)
boundary_transfer: $(BUILD_DIR)/boundary_transfer$(EXE)

$(BUILD_DIR)/course_exchange$(EXE): $(SEARCH_SOURCES) Makefile | $(BUILD_DIR)
	"$(CXX)" $(CPPFLAGS) $(CXXFLAGS) -MMD -MP -MF $(BUILD_DIR)/course_exchange.d $< $(LDFLAGS) $(LDLIBS) -o "$@"

$(BUILD_DIR)/%$(EXE): tools/verification/%.cpp Makefile | $(BUILD_DIR)
	"$(CXX)" $(CPPFLAGS) $(CXXFLAGS) -MMD -MP -MF $(BUILD_DIR)/$*.d $< $(LDFLAGS) $(LDLIBS) -o "$@"

$(BUILD_DIR)/paint-waste$(EXE): tools/reduced_alphabet.cpp Makefile | $(BUILD_DIR)
	"$(CXX)" $(CPPFLAGS) $(PAINT_CXXFLAGS) -MMD -MP -MF $(BUILD_DIR)/paint-waste.d $< $(LDFLAGS) $(LDLIBS) -o "$@"

$(BUILD_DIR)/boundary_transfer$(EXE): $(LIB_DIR)/boundary_transfer.cpp $(LIB_DIR)/construct.cpp Makefile | $(BUILD_DIR)
	"$(CXX)" $(CPPFLAGS) $(CXXFLAGS) -MMD -MP -MF $(BUILD_DIR)/boundary_transfer.d $< $(LDFLAGS) $(LDLIBS) -o "$@"

$(BUILD_DIR):
ifeq ($(OS),Windows_NT)
	if not exist "$@" mkdir "$@"
else
	mkdir -p "$@"
endif

# Remove only this Makefile's named outputs; leave the build directory in place.
clean:
ifeq ($(OS),Windows_NT)
	for %%f in ($(subst /,\,$(BINARIES) $(DEPFILES))) do @if exist "%%f" del /Q "%%f"
else
	rm -f $(BINARIES) $(DEPFILES)
endif

-include $(DEPFILES)
