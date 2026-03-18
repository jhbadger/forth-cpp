CXX = g++
PREFIX = $(HOME)
DIR = $(shell pwd)
CXXFLAGS = -O -DDIR=\""$(DIR)\"" -std=c++17 -o forth
TARGET = forth
SOURCE = forth.cpp
PREFIX = $(HOME)

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SOURCE)

install: $(TARGET)
	cp $(TARGET) $(PREFIX)/bin

clean:
	rm -f $(TARGET)

.PHONY: all clean
