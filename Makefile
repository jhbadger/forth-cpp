CXX = g++
PREFIX = $(HOME)
DIR = $(shell pwd)
CXXFLAGS = -O -DUSE_READLINE -DDIR=\""$(DIR)\"" -std=c++17 -o forth
TARGET = forth
SOURCE = forth.cpp
LIBS = -lreadline # remove if not USE_READLINE
PREFIX = $(HOME)

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SOURCE) $(LIBS)

install: $(TARGET)
	cp $(TARGET) $(PREFIX)/bin

clean:
	rm -f $(TARGET)

.PHONY: all clean
