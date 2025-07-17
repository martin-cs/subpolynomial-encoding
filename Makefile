CXXFLAGS+=-Wall -W -O3 -std=c++17
CVC5INSTALL=/home/city/install/cvc5
TAREGTS=subpolynomial_experiment_generator
.PHONY=all clean run

all : $(TARGETS)

clean :
	rm -v *.o $(TARGETS)

run : subpolynomial_experiment_generator
	LD_LIBRARY_PATH=$(CVC5INSTALL)/lib/ ./subpolynomial_experiment_generator 8 12 23


subpolynomial_experiment_generator : subpolynomial_experiment_generator.o rewriter.o
	$(CXX) $^ $(CVC5INSTALL)/lib/libcvc5.so -o $@

%.o : %.cpp
	$(CXX) -c $(CXXFLAGS) -I$(CVC5INSTALL)/include/ $^ -o $@

