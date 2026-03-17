# Compiler and flags
CXX = g++
DIR = $(shell pwd) # change if you want a different directory for stdlib.fs
CXXFLAGS = -O -DDIR=\""$(DIR)\"" -std=c++17 -o forth

# Source files
SRC = forth.cpp

# Target executable
TARGET = forth

# Default rule: builds the executable
all: $(TARGET)

# Build rule for the executable
$(TARGET): $(SRC)
	$(CXX) $(CXXFLAGS) $(SRC)

# Clean rule: removes the executable
clean:
	rm -f $(TARGET)

# Phony targets (targets that don't represent files)
.PHONY: all clean
