.SUFFIXES: .cpp .o
CC=g++
CFLAGS=-c -std=c++0x -I../fxt/include/ -O3 -DNDEBUG
LDFLAGS=-static
SOURCES=drawsgtree.cpp
OBJECTS=$(SOURCES:.cpp=.o)
EXECUTABLE=drawsgtree
OTHERS=Makefile
ZIP=zip
ZIPFILE=drawsgtree.zip

all: $(EXECUTABLE) $(ZIPFILE)

$(EXECUTABLE): $(OBJECTS)
	$(CC) $(OBJECTS) $(LDFLAGS) -o $@

.cpp.o:
	$(CC) $(CFLAGS) $< -o $@

$(ZIPFILE): $(SOURCES) $(OTHERS)
	$(ZIP) $(ZIPFILE) $(SOURCES) $(OTHERS)

clean:
	rm -f $(OBJECTS) $(EXECUTABLE) $(ZIPFILE)
