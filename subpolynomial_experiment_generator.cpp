/*
** subpolynomial_experiment_generator.cpp
**
** Martin Brain
** martin.brain@citystgeorges.ac.uk
** 07/03/25
**
** Generate a set of SMT files to compare different polynomial
** encoding strategies, including using subpolynomials.
**
*/

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <memory>
#include <string>
#include <strstream>

#include <cvc5/cvc5.h>

#define USE_BV 1

#include "binary_polynomial.h"
#include "rewriter.h"

using namespace cvc5;

void outputPolynomial(const binary_polynomial &p, Term x) {
  //  std::cout << p.degree() << " : " << p.eval(x) << std::endl << std::endl;
  std::cout << p.degree() << " : " << p << std::endl << std::endl;
  return;
}

Term makeTrue(TermManager &tm) {
  #ifdef USE_BV
  return tm.mkBitVector(1,1u);
  #else
  return tm.mkBoolean(true);
  #endif
}

Term makeFalse(TermManager &tm) {
  #ifdef USE_BV
  return tm.mkBitVector(1,0u);
  #else
  return tm.mkBoolean(false);
  #endif
}

Term makeBit(TermManager &tm, const std::string &name) {
  #ifdef USE_BV
  return tm.mkConst(tm.mkBitVectorSort(1), name); 
  #else
  return tm.mkConst(tm.getBooleanSort(), name); 
  #endif
}

Term makeLiteral(TermManager &tm, uint32_t bitWidth, uint32_t val) {
  #ifdef USE_BV
  return tm.mkBitVector(bitWidth, val);
  #else
  return tm.mkInteger(val);
  #endif
}

#define SAT 1
#define UNSAT 0
#define UNKNOWN -1

void createFile(const std::string &fileName, const std::string &description, Term x, Term assertion, int status = UNKNOWN) {
  std::ofstream output(fileName);

  output << "(set-info :smt-lib-version 2.6)" << std::endl;
  output << "(set-logic QF_BV)" << std::endl;
  output << "(set-info :source |Generate by subpolynomial_experiment_generator by Martin Brain to investigate the properties of the subpolynomial encoding of polynomials. " << description << "|)" << std::endl;
  output << "(set-info :license \"https://creativecommons.org/licenses/by/4.0/\")" << std::endl;
  output << "(set-info :category crafted)" << std::endl;
  
  output << "(set-info :status ";
  switch (status) {
  case SAT : output << "sat"; break;
  case UNSAT : output << "unsat"; break;
  case UNKNOWN : output << "unknown"; break;
  default :
    assert(0);
  }
  output << ")" << std::endl;
  
  output << "(set-option :produce-models true)" << std::endl;
  output << "(declare-const " << x << " " << x.getSort() << ")" << std::endl;
  
  output << "(assert " << assertion << " )" << std::endl << std::endl;
  
  output << "(check-sat)" << std::endl;
  output << "(get-value (x))" << std::endl;
  output.close();

  return;
}



int main(int argc, char **argv)
{
  if (argc != 4) {
    std::cerr << "Usage : " << argv[0] << " bitWidth degree randomSeed" << std::endl;
    return 1;
  }
  //uint32_t bitWidth = 8;
  //uint32_t bitWidth = 64;
  uint32_t bitWidth = std::stoul(argv[1]);
  uint32_t degree = std::stoul(argv[2]);
  unsigned int seed = std::stoul(argv[3]);

  // Seed the random number generator for reproducibility
  std::srand(seed);
  
  
  TermManager tm;

  std::shared_ptr<Solver> slv = std::make_shared<Solver>(tm);
  #ifdef USE_BV
  slv->setLogic("QF_BV");
  #else
  slv->setLogic("QF_NIA");
  #endif
  slv->setOption("produce-models", "true");
  rewriter::setRewriterSolver(slv);
  
  #ifdef USE_BV
  Sort s = tm.mkBitVectorSort(bitWidth);
  Term x = tm.mkConst(s, "x");
  Term x4 = tm.mkConst(tm.mkBitVectorSort(4), "x");
  Term x3 = tm.mkConst(tm.mkBitVectorSort(3), "x");
  Term x2 = tm.mkConst(tm.mkBitVectorSort(2), "x");
  Term x1 = tm.mkConst(tm.mkBitVectorSort(1), "x");
  #else
  Sort s = tm.getIntegerSort();
  Term x = tm.mkConst(s, "x");
  Term x4 = x;
  Term x3 = x;
  Term x2 = x;
  Term x1 = x;
  #endif

  /*** Unit tests for infrastructure ***/
  #if 0
  binary_polynomial zero(tm, bitWidth);
  std::cout << "Zero" << std::endl;
  outputPolynomial(zero, x);
  
  binary_polynomial squared(tm, bitWidth, 1u, 2);
  std::cout << "x^2" << std::endl;
  outputPolynomial(squared, x);

  binary_polynomial cubed(tm, bitWidth, 7u, 3);
  std::cout << "7x^3" << std::endl;
  outputPolynomial(cubed, x);
  
  binary_polynomial p(tm, bitWidth, {1u, 3u, 3u, 1u});
  std::cout << "p" << std::endl;
  outputPolynomial(p, x);
  
  #ifdef USE_BV
  binary_polynomial q(tm, bitWidth, {tm.mkBitVector(bitWidth, 1u), tm.mkBitVector(bitWidth, 3u), tm.mkBitVector(bitWidth, 3u), tm.mkBitVector(bitWidth, 1u)});
  #else
  binary_polynomial q(tm, bitWidth, {1u, 3u, 3u, 1u});
  #endif
  std::cout << "q" << std::endl;
  outputPolynomial(q, x);
  
  binary_polynomial sum = p + q;
  std::cout << "p+q" << std::endl;
  outputPolynomial(sum, x);
  
  binary_polynomial addition = zero + (cubed + squared);
  std::cout << "7x^3 + x^2" << std::endl;
  outputPolynomial(addition, x);
  
  binary_polynomial addition2 = (zero + cubed) + squared;
  std::cout << "7x^3 + x^2" << std::endl;
  outputPolynomial(addition2, x);
  
  binary_polynomial subtraction = zero - (cubed - squared);
  std::cout << "-7x^3 + x^2" << std::endl;
  outputPolynomial(subtraction, x);
  
  binary_polynomial subtraction2 = (zero - cubed) - squared;
  std::cout << "-7x^3 -x^2" << std::endl;
  outputPolynomial(subtraction2, x);
  
  binary_polynomial multiplication = cubed * squared;
  std::cout << "7x^5" << std::endl;
  outputPolynomial(multiplication, x);
  
  binary_polynomial multiplication2 = cubed * zero;
  std::cout << "0" << std::endl;
  outputPolynomial(multiplication2, x);
  #endif

  /*** Unit tests for reduction ***/
  #if 0
  assert(bitWidth == 8);
  binary_polynomial zpf_order_2_8_bit(tm, bitWidth, {0u, 128u, 128u});
  std::cout << "8 bit, degree 2 ZFP" << std::endl;
  std::cout << "Is a ZPF? " << zpf_order_2_8_bit.valueEqual(zero) << std::endl;
  outputPolynomial(zpf_order_2_8_bit, x);
  
  binary_polynomial reduced_2_8_bit = zpf_order_2_8_bit.reduce();
  std::cout << "0" << std::endl;
  outputPolynomial(reduced_2_8_bit, x);



  
  binary_polynomial zpf_order_4_8_bit(tm, bitWidth, {0u, 192u, 352u, 192u, 32u});
  std::cout << "8 bit, degree 4 ZFP" << std::endl;
  std::cout << "Is a ZPF? " << zpf_order_4_8_bit.valueEqual(zero) << std::endl;
  outputPolynomial(zpf_order_4_8_bit, x);
  
  binary_polynomial reduced_4_8_bit = zpf_order_4_8_bit.reduce();
  std::cout << "0" << std::endl;
  outputPolynomial(reduced_4_8_bit, x);


  
  
  binary_polynomial zpf_order_6_8_bit(tm, bitWidth, {0u, 1920u, 4384u, 3600u, 1360u, 240u, 16u});
  std::cout << "8 bit, degree 6 ZFP" << std::endl;
  std::cout << "Is a ZPF? " << zpf_order_6_8_bit.valueEqual(zero) << std::endl;
  outputPolynomial(zpf_order_6_8_bit, x);
  
  binary_polynomial reduced_6_8_bit = zpf_order_6_8_bit.reduce();
  std::cout << "0" << std::endl;
  outputPolynomial(reduced_6_8_bit, x);
  


  binary_polynomial zpf_order_8_8_bit(tm, bitWidth, {0u, 10080u, 26136u, 26264u, 13538u, 3920u, 644u, 56u, 2u});
  std::cout << "8 bit, degree 8 ZFP" << std::endl;
  std::cout << "Is a ZPF? " << zpf_order_8_8_bit.valueEqual(zero) << std::endl;
  outputPolynomial(zpf_order_8_8_bit, x);
  
  binary_polynomial reduced_8_8_bit = zpf_order_8_8_bit.reduce();
  std::cout << "0" << std::endl;
  outputPolynomial(reduced_8_8_bit, x);
  

  binary_polynomial zpf_order_10_8_bit(tm, bitWidth, {0u, 362880u, 1026576u, 1172700u, 723680u, 269325u, 63273u, 9450u, 870u, 45u, 1u});
  std::cout << "8 bit, degree 10 ZFP" << std::endl;
  std::cout << "Is a ZPF? " << zpf_order_10_8_bit.valueEqual(zero) << std::endl;
  outputPolynomial(zpf_order_10_8_bit, x);
  
  binary_polynomial reduced_10_8_bit = zpf_order_10_8_bit.reduce();
  std::cout << "0" << std::endl;
  outputPolynomial(reduced_10_8_bit, x);


  // Test the reduction on things that are not ZFPs...
  binary_polynomial order15(tm, bitWidth, {15u, 1u, 2u, 3u, 4u, 5u, 6u, 7u, 8u, 9u, 10u, 11u, 12u, 13u, 14u, 15u});
  std::cout << "order15" << std::endl;
  outputPolynomial(order15, x);

  binary_polynomial reduced(order15.reduce());
  std::cout << "reduced" << std::endl;
  std::cout << "Is equal? " << order15.valueEqual(reduced) << std::endl;
  outputPolynomial(reduced, x);
#endif


  /*** Unit tests for subpolynomials from the paper ***/
#if 0
  assert(bitWidth == 4);
  //binary_polynomial jacobsExample(tm, bitWidth, {0u,2u,2u,1u});
  binary_polynomial jacobsExample(tm, bitWidth, {3u, 3u, 2u, 4u});
  std::cout << "Jacob's Example" << std::endl;
  outputPolynomial(jacobsExample, x4);

  binary_polynomial f0(jacobsExample.subpolynomial(makeFalse(tm)));
  std::cout << "f0 before divide by 2" << std::endl;
  outputPolynomial(f0, x4);
  binary_polynomial f0_2(f0.topBits());
  std::cout << "f0" << std::endl;
  outputPolynomial(f0_2, x3);
  
  
  binary_polynomial f1(jacobsExample.subpolynomial(makeTrue(tm)));
  std::cout << "f1 before divide by 2" << std::endl;
  outputPolynomial(f1, x4);
  binary_polynomial f1_2(f1.topBits());
  std::cout << "f1" << std::endl;
  outputPolynomial(f1_2, x3);

  binary_polynomial f00(f0_2.subpolynomial(makeFalse(tm)));
  std::cout << "f00 before divide by 2" << std::endl;
  outputPolynomial(f00, x3);
  binary_polynomial f00_2(f00.topBits());
  std::cout << "f00" << std::endl;
  outputPolynomial(f00_2, x2);
  
  binary_polynomial f11(f1_2.subpolynomial(makeTrue(tm)));
  std::cout << "f11 before divide by 2" << std::endl;
  outputPolynomial(f11, x3);
  binary_polynomial f11_2(f11.topBits());
  std::cout << "f11" << std::endl;
  outputPolynomial(f11_2, x2);
  

  Term b0 = makeBit(tm, "b0");
  binary_polynomial sub0(jacobsExample.subpolynomial(b0));
  std::cout << "Subpolynomial 0 before divide by 2" << std::endl;
  outputPolynomial(sub0, x4);
  binary_polynomial sub0_2(sub0.topBits());
  std::cout << "Subpolynomial 0" << std::endl;
  outputPolynomial(sub0_2, x3);    

  Term b1 = makeBit(tm, "b1");
  binary_polynomial sub1(sub0_2.subpolynomial(b1));
  std::cout << "Subpolynomial 1 before divide by 2" << std::endl;
  outputPolynomial(sub1, x3);
  binary_polynomial sub1_2(sub1.topBits());
  std::cout << "Subpolynomial 1" << std::endl;
  outputPolynomial(sub1_2, x2);    

  Term b2 = makeBit(tm, "b2");
  binary_polynomial sub2(sub1_2.subpolynomial(b2));
  std::cout << "Subpolynomial 2 before divide by 2" << std::endl;
  outputPolynomial(sub2, x2);
  binary_polynomial sub2_2(sub2.topBits());
  std::cout << "Subpolynomial 2" << std::endl;
  outputPolynomial(sub2_2, x1);    

  Term b3 = makeBit(tm, "b3");
  binary_polynomial sub3(sub2_2.subpolynomial(b3));
  std::cout << "Subpolynomial 3 before divide by 2" << std::endl;
  outputPolynomial(sub3, x1);
  /*
  binary_polynomial sub3_2(sub3.topBits());
  std::cout << "Subpolynomial 3" << std::endl;
  outputPolynomial(sub3_2, x0???);
  */
#endif

#if 0
  assert(bitWidth == 8);
  binary_polynomial zfp(tm, bitWidth, {0u, 1920u, 4384u, 3600u, 1360u, 240u, 16u});
  binary_polynomial arbitrary(tm, bitWidth, {4u, 11u, 17u, 45u, 3u, 0u, 0u, 93u, 23u, 0u, 5u});
  binary_polynomial stillAZFP(zfp * arbitrary);

  /*** Unit tests for encoding generation ***/
  binary_polynomial permutation(tm, bitWidth, {7u, 7u, 7u, 7u, 5u, 5u});  // Actually reducible to degree 5

  binary_polynomial start(permutation + stillAZFP);
  std::cout << "Start " << std::endl;
  outputPolynomial(start, x);

  // Brute force find roots
  for (uint32_t i = 0; i < (1ULL << bitWidth); ++i) {
    Term input = makeLiteral(tm,bitWidth, i);
    Term output = slv->simplify(start.eval(input));
    std::cout << input << " ~~> " << output << std::endl;    
  }

  // Output
  createFile("original.smt2", x, tm.mkTerm(Kind::EQUAL, { makeLiteral(tm,bitWidth, 0u), start.eval(x) }));
  
  binary_polynomial startReduced(start.reduce());
  std::cout << "Start reduced " << std::endl;
  outputPolynomial(startReduced, x);

  // Sanity check the reduction
  std::cout << "Is equal? " << start.valueEqual(startReduced) << std::endl;

  // Output
  createFile("reduced.smt2", x, tm.mkTerm(Kind::EQUAL, { makeLiteral(tm,bitWidth, 0u), startReduced.eval(x) })); 
  

  std::ofstream encode("encode.smt2");
  encode << "(set-logic QF_BV)" << std::endl;
  encode << "(set-option :produce-models true)" << std::endl;
  encode << "(declare-const x (_ BitVec " << bitWidth << "))" << std::endl;

  
  binary_polynomial working = startReduced;
  Term var = x;
  
  Term shouldBeARoot = makeLiteral(tm, bitWidth, 255u);
  std::vector<Term> from;
  std::vector<Term> to;
  
  for (uint32_t i = 0; i < bitWidth; ++i) {
    std::cout << std::endl << std::endl;
    std::cout << i << " var " << var << std::endl << std::endl;
    std::cout << i << " working " << working << std::endl << std::endl;

    // Substitute out the low bits of the root
    binary_polynomial partialSolution(working.substitute(from,to));
    std::cout << i << " partialSolution " << partialSolution << std::endl << std::endl;

    // Check the rest still works
    std::cout << i << " Should be zero " << rewriter::rewrite(partialSolution.eval(shouldBeARoot)) << std::endl << std::endl;

    
    Term lsbOutput = working.lsb(var);
    std::cout << i << " lsbOutput " << lsbOutput << std::endl << std::endl;

    encode << "(assert (= " << makeLiteral(tm, 1, 0) << " " << lsbOutput << " ) )" << std::endl << std::endl;

    
    // Try to simplify with previous assertions
    // slv->simplify(lsbOutput, true) should do this but doesn't seem to work
    if (from.size() >= 1) {
      Term lsbOutputSimplified = rewriter::rewrite(lsbOutput.substitute(from, to));
      std::cout << i << " lsbOutputSimplified " << lsbOutputSimplified << std::endl << std::endl;
    }
    
    // Make it equal to zero
    Term zero(makeLiteral(tm,1,0u));
    slv->assertFormula(tm.mkTerm(Kind::EQUAL, {lsbOutput, zero}));

    
    // An actual example of a split while loop!
    if (i + 1u == bitWidth) {
      break;
    }

    // Now let's start on the subpolynomial step
    Term lsbInput = working.extractLSB(var);
    Term restInput = working.extractTopBits(var);
    
    Term bit;
    #ifdef USE_BV
    bit = lsbInput;
    #else
    bit = tm.mkTerm(Kind::EQUAL, {lsbInput, makeLiteral(tm, bitWidth, 1)});
    #endif
    binary_polynomial sub = working.subpolynomial(bit);

    // Save the low bits of the root in the substitution map
    from.push_back(lsbInput);
    to.push_back(working.extractLSB(shouldBeARoot));
    std::cout << i << " " << from[i] << " ~~> " << to[i] << std::endl << std::endl;
    
    std::cout << i << " Subpolynomial " << sub << std::endl << std::endl;
    std::cout << i << " Subpolynomial substituted " << sub.substitute(from,to) << std::endl << std::endl;
    std::cout << i << " Still should be zero " << rewriter::rewrite(sub.substitute(from,to).eval(shouldBeARoot)) << std::endl << std::endl;

    // Now get the top bits
    binary_polynomial subDiv2 = sub.topBits();

    
    var = restInput;
    shouldBeARoot = working.extractTopBits(shouldBeARoot);
    working = subDiv2;

    std::cout << i << " Subpolynomial/2 " << subDiv2 << std::endl << std::endl;
    std::cout << i << " Subpolynomial/2 substituted " << subDiv2.substitute(from,to) << std::endl << std::endl;
    std::cout << i << " Really should be zero " << rewriter::rewrite(subDiv2.substitute(from,to).eval(shouldBeARoot)) << std::endl << std::endl;
  }

  encode << "(check-sat)" << std::endl;
  encode << "(get-value (x))" << std::endl;
  encode.close();
  
  // Sanity check
  std::cout << slv->checkSat() << std::endl;
  Term root = slv->getValue(x);
  std::cout << "x = " << root << std::endl;

  Term finalCheck = slv->simplify(start.eval(root));
  std::cout << "finalCheck = " << finalCheck << std::endl;
#endif  


#if 0
  // Test ZFP generation
  binary_polynomial zeroP(binary_polynomial(tm, bitWidth));
  for (size_t i = 0; i <= bitWidth + 2; ++i) {
    binary_polynomial zfp(binary_polynomial::zfp(tm, bitWidth, i));
    std::cout << zfp << std::endl;

    std::cout << zfp.valueEqual(zeroP) << std::endl;
  }
#endif
  
  // Actual functionality!

// Using permutation polynomials guarantees that root finding is SAT and has exactly one model
// Eabed for the SMT25 experiments
#define P_IS_PERMUTATION
  #ifdef P_IS_PERMUTATION
  binary_polynomial p(binary_polynomial::randomPermutationPolynomial(tm, bitWidth, degree));
  #else
  binary_polynomial p(binary_polynomial::random(tm, bitWidth, degree));
  #endif
  Term p_x = p.eval(x);
  Term p_enc = p.encode(x);
  
  binary_polynomial pReduced = p.reduce();
  Term pReduced_x = pReduced.eval(x);
  Term pReduced_enc = pReduced.encode(x);

// The full set of experiments were not used for the SMT25 paper
//#define FULL_EXPERIMENTS
#ifdef FULL_EXPERIMENTS
  binary_polynomial q(binary_polynomial::random(tm, bitWidth, degree));
  Term q_x = q.eval(x);
  Term q_enc = q.encode(x);
  
  binary_polynomial qReduced = q.reduce();
  Term qReduced_x = qReduced.eval(x);
  Term qReduced_enc = qReduced.encode(x);
#endif
  
  std::strstream str1;
  str1 << "bitwidth-" << bitWidth << "-degree-" << degree << "-seed-" << seed << std::ends;
  std::string prefix(str1.str());

  std::strstream str2;
  str2 << "p(x) = " << p << " . " << std::ends;
  std::string generalP(str2.str());

#ifdef FULL_EXPERIMENTS
  std::strstream str3;
  str3 << "p(x) = " << p << " q(x) = " << q << " . " << std::ends;
  std::string generalPQ(str3.str());
#endif
  
  // Root finding
  {
    std::string description = generalP + "This benchmark tests root finding, i.e. p(x) = 0.";
  
    Term zero = makeLiteral(tm,bitWidth, 0u);

#ifdef P_IS_PERMUTATION
    int status = SAT;
#else
    int status = UNKNOWN;
#endif
  
    createFile(prefix + "-root-finding-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { zero , p_x }), status);
    createFile(prefix + "-root-finding-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { zero, p_enc }), status);
    createFile(prefix + "-root-finding-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { zero, pReduced_x }), status);
    createFile(prefix + "-root-finding-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { zero, pReduced_enc }), status);
  }

  // Identity finding
  {
    std::string description = generalP + "This benchmark tests identity finding, i.e. p(x) = x.";
  
    createFile(prefix + "-identity-point-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { x , p_x }));
    createFile(prefix + "-identity-point-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { x, p_enc }));
    createFile(prefix + "-identity-point-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { x, pReduced_x }));
    createFile(prefix + "-identity-point-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { x, pReduced_enc }));  
  }

#ifdef FULL_EXPERIMENTS
  // Bounding
  {
    std::string description = generalP + "This benchmark tests bounds, i.e. p(x) < const.";
  
    Term bound = p.random();
    createFile(prefix + "-bounding-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::BITVECTOR_ULT, { bound , p_x }));
    createFile(prefix + "-bounding-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::BITVECTOR_ULT, { bound, p_enc }));
    createFile(prefix + "-bounding-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::BITVECTOR_ULT, { bound, pReduced_x }));
    createFile(prefix + "-bounding-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::BITVECTOR_ULT, { bound, pReduced_enc }));  
  }

  // Encoding correctness
  {
    std::string description = generalP + "This benchmark tests the equivalence of the various encodings";
  
    createFile(prefix + "-correctness-original-native-encoding-vs-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, { tm.mkTerm(Kind::EQUAL, { p_x, pReduced_x }) }), UNSAT);
    createFile(prefix + "-correctness-original-native-encoding-vs-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, { tm.mkTerm(Kind::EQUAL, { p_x, p_enc }) }), UNSAT);
    createFile(prefix + "-correctness-original-native-encoding-vs-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, { tm.mkTerm(Kind::EQUAL, { p_x, pReduced_enc }) }), UNSAT);
    createFile(prefix + "-correctness-reduced-native-encoding-vs-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, { tm.mkTerm(Kind::EQUAL, { pReduced_x, p_enc }) }), UNSAT);
    createFile(prefix + "-correctness-reduced-native-encoding-vs-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, { tm.mkTerm(Kind::EQUAL, { pReduced_x, pReduced_enc }) }), UNSAT);
    createFile(prefix + "-correctness-original-subpolynomial-encoding-vs-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, { tm.mkTerm(Kind::EQUAL, { p_enc, pReduced_enc }) }), UNSAT);
  }

  
  // Equality
  {
    std::string description = generalPQ + "This benchmark tests for find points of equality between two polynomials, i.e. p(x) = q(x).";
    
    createFile(prefix + "-equality-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { p_x, q_x }));
    createFile(prefix + "-equality-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { p_enc, q_enc }));
    createFile(prefix + "-equality-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { pReduced_x, qReduced_x }));
    createFile(prefix + "-equality-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::EQUAL, { pReduced_enc, qReduced_enc }));  
  }

  // Non-equality
  {
    std::string description = generalPQ + "This benchmark tests for find points of non-equality between two polynomials, i.e. p(x) != q(x).";
    
    createFile(prefix + "-nonequality-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, { p_x, q_x })}));
    createFile(prefix + "-nonequality-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, { p_enc, q_enc })}));
    createFile(prefix + "-nonequality-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, { pReduced_x, qReduced_x })}));
    createFile(prefix + "-nonequality-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, { pReduced_enc, qReduced_enc })}));
  }

  // Addition
  {
    std::string description = generalPQ + "This benchmark tests whether p(x) + q(x) = (p + q)(x).";

    binary_polynomial pq(p + q);
    Term pq_x = pq.eval(x);
    Term pq_enc = pq.encode(x);
    
    binary_polynomial pqReduced = pq.reduce();
    Term pqReduced_x = pqReduced.eval(x);
    Term pqReduced_enc = pqReduced.encode(x);

      
    createFile(prefix + "-addition-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_ADD, { p_x, q_x }), pq_x})}), UNSAT);
    createFile(prefix + "-addition-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_ADD, { p_enc, q_enc }), pq_enc})}), UNSAT);
    createFile(prefix + "-addition-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_ADD, { pReduced_x, qReduced_x }), pqReduced_x})}), UNSAT);
    createFile(prefix + "-addition-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_ADD, { pReduced_enc, qReduced_enc }), pqReduced_enc})}), UNSAT);
  }
  
  // Multiplication
  {
    std::string description = generalPQ + "This benchmark tests whether p(x) * q(x) = (p * q)(x).";

    binary_polynomial pq(p * q);
    Term pq_x = pq.eval(x);
    Term pq_enc = pq.encode(x);
    
    binary_polynomial pqReduced = pq.reduce();
    Term pqReduced_x = pqReduced.eval(x);
    Term pqReduced_enc = pqReduced.encode(x);

      
    createFile(prefix + "-multiplication-original-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_MULT, { p_x, q_x }), pq_x})}), UNSAT);
    createFile(prefix + "-multiplication-original-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_MULT, { p_enc, q_enc }), pq_enc})}), UNSAT);
    createFile(prefix + "-multiplication-reduced-native-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_MULT, { pReduced_x, qReduced_x }), pqReduced_x})}), UNSAT);
    createFile(prefix + "-multiplication-reduced-subpolynomial-encoding.smt2", description, x, tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::EQUAL, {tm.mkTerm(Kind::BITVECTOR_MULT, { pReduced_enc, qReduced_enc }), pqReduced_enc})}), UNSAT);
  }
#endif
  

// TODO
// bounding input / bounded output
// polynomial composition

  
  // The solver goes out of scope before the global gets garbage collected
  rewriter::setRewriterSolver(nullptr);

  return 0;
}

