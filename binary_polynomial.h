/*
** binary_polynomial.h
**
** Martin Brain
** martin.brain@citystgeorges.ac.uk
** 07/03/25
**
** A class to represent bit-vector polynomials.
** Uses a dense representation in normal form.
** So evaluation is coeff[0] + x*coeff[1] + x^2*coeff[2] + ...
**
*/

#include <algorithm>
#include <cstdlib>
#include <vector>

#include <cvc5/cvc5.h>

#include <stdint.h>

#include "rewriter.h"

#ifndef BINARY_POLYNOMIAL_H
#define BINARY_POLYNOMIAL_H

using namespace cvc5;

class binary_polynomial {
 public :
  //protected:  // Should be at least protected, if not correctly encapsulated elsewhere
  // To allow easier switching between number systems,
  // these are some simple wrappers for Term creation
  Term constant(uint64_t c) const {
#ifdef USE_BV
    return tm.mkBitVector(w,c);
#else
    return tm.mkInteger(c);
#endif
  }

  Term random() const {
    Term zero(constant(0u));
    Term one(constant(1u));
    Term two(constant(2u));
    Term working = zero;
    
    for (size_t i = 0; i < w; ++i) {
      // This is kind of slow and wasteful
      // but it does work with both number systems and any bitWidth regardless of RAND_MAX
      int r = rand();

      if ((r & 0x1) == 0x1) {
	working = add({working, one});
      } else {
	working = add({working, zero});
      }

      if (i + 1 == w) {
	break;
      } else {
	working = mult({working, two});
      }
    }

    return rewriter::rewrite(working);
  }
  
  Term powerOfTwo(uint64_t c) const {
    Term n = constant(1);
    Term two = constant(2);
    for (uint64_t i = 0; i < c; ++i) {// Yes this is kind of stupid
      n = mult({n,two});              // But it avoids overflow and USE_BV
    }
    return rewriter::rewrite(n);
  }
  Term mult(const std::vector<Term> &op) const {
#ifdef USE_BV
    return tm.mkTerm(Kind::BITVECTOR_MULT,op);
#else
    return tm.mkTerm(Kind::MULT,op);
#endif
  }
  Term add(const std::vector<Term> &op) const {
#ifdef USE_BV
    return tm.mkTerm(Kind::BITVECTOR_ADD,op);
#else
    return tm.mkTerm(Kind::ADD,op);
#endif
  }
  Term sub(const std::vector<Term> &op) const {
#ifdef USE_BV
    return tm.mkTerm(Kind::BITVECTOR_SUB,op);
#else
    return tm.mkTerm(Kind::SUB,op);
#endif
  }
  Term neg(const std::vector<Term> &op) const {
#ifdef USE_BV
    return tm.mkTerm(Kind::BITVECTOR_NEG,op);
#else
    return tm.mkTerm(Kind::NEG,op);
#endif
  }
  Term mod(const std::vector<Term> &op) const {
#ifdef USE_BV
    return rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_UREM,op));
#else
    return rewriter::rewrite(tm.mkTerm(Kind::INTS_MODULUS,op));
#endif
  }
  Term extractTopBits(const Term &op) const {
#ifdef USE_BV
    return rewriter::rewrite(tm.mkTerm(tm.mkOp(Kind::BITVECTOR_EXTRACT, {w-1, 1}), {op}));
#else
    return rewriter::rewrite(tm.mkTerm(Kind::INTS_DIVISION,{op, constant(2u)}));
#endif
  }
  Term extractLSB(const Term &op) const {
#ifdef USE_BV
    return rewriter::rewrite(tm.mkTerm(tm.mkOp(Kind::BITVECTOR_EXTRACT, {0, 0}), {op}));
#else
    return rewriter::rewrite(tm.mkTerm(Kind::INTS_MODULUS,{op, constant(2u)}));
#endif
  }
  
  
  Term ite(const std::vector<Term> &op) const {
#ifdef USE_BV
    Term mask = tm.mkTerm(tm.mkOp(Kind::BITVECTOR_REPEAT, {w}), {op[0]});
    Term nmask = tm.mkTerm(Kind::BITVECTOR_NOT, {mask});
    Term l = rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_AND, {mask, op[1]}));
    Term r = rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_AND, {nmask, op[2]}));
    return rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_OR, {l, r}));
#else
    return tm.mkTerm(Kind::ITE, op);
#endif
  }

  #define TRUE 1
  #define FALSE 0
  #define UNKNOWN -1
  
  // Only works if it can rewrite to equal
  // equal -> 1, not equal -> 0, unknown -> -1
  int simpleTermEqual(Term left, Term right) const {
    Term res = rewriter::rewrite(tm.mkTerm(Kind::EQUAL, {left, right}));
    if (res.isBooleanValue()) {
      if (res.getBooleanValue()) {
	return TRUE;
      } else {
	return FALSE;
      }
    } else {
      return UNKNOWN;
    }
  }
  
 public:
  // Zero
 binary_polynomial(TermManager &_tm, uint32_t wordSize) : tm(_tm), w(wordSize), bv(tm.mkBitVectorSort(w)) {
    coeff.push_back(constant(0u));
 }

  // Monomial or constant
 binary_polynomial(TermManager &_tm, uint32_t wordSize, Term coefficient, size_t degree = 0) : tm(_tm), w(wordSize), bv(tm.mkBitVectorSort(w)) {
    for (uint32_t i = 0; i < degree; ++i) {
      coeff.push_back(constant(0u));
    }
    coeff.push_back(coefficient);
  }

 binary_polynomial(TermManager &_tm, uint32_t wordSize, uint64_t c, size_t degree = 0) : tm(_tm), w(wordSize), bv(tm.mkBitVectorSort(w)) {
    for (uint32_t i = 0; i < degree; ++i) {
      coeff.push_back(constant(0u));
    }
    coeff.push_back(constant(c));
  }

  // More complex literal polynomials
 binary_polynomial(TermManager &_tm, uint32_t wordSize, std::vector<uint64_t> coefficients) : tm(_tm), w(wordSize), bv(tm.mkBitVectorSort(w)) {
    for (uint32_t i = 0; i < coefficients.size(); ++i) {
      coeff.push_back(constant(coefficients[i]));
    }
    compact();
  }
  
  // More complex polynomials 
 binary_polynomial(TermManager &_tm, uint32_t wordSize, std::vector<Term> coefficients) : tm(_tm), w(wordSize), bv(tm.mkBitVectorSort(w)), coeff(coefficients) {
    compact();
  }

  // Copy constructor
 binary_polynomial(const binary_polynomial &old) : tm(old.tm), w(old.w), bv(old.bv), coeff(old.coeff) {
    compact();
  }


  // Computes the minimum two addic valuation of a factorial normal form monomial x^{(i)}
  static size_t minimumTwoAddic(size_t i) {
    size_t minimumTwoAddicVal = 0;
    size_t j = i/2;
    while (j > 0) {
      minimumTwoAddicVal += j;
      j = j/2;
    }

    return minimumTwoAddicVal;
  }

  Term minimumTwoAddicValuationTerm(size_t minimumTwoAddicVal) {
    if (w >= minimumTwoAddicVal) {
      return powerOfTwo(w - minimumTwoAddicVal);
    } else {
      return constant(1u);
    }
  }  

  static binary_polynomial zfp(TermManager &tm, uint32_t wordSize, size_t degree) {
    if (degree == 0) {
      return binary_polynomial(tm, wordSize);
    } else {    
      binary_polynomial x(tm, wordSize, 1, 1);  // x!
      binary_polynomial working(x);
      for (size_t i = 2; i <= degree; ++i) {
	binary_polynomial constant(tm, wordSize, i-1);
	working = working * (x + constant);  // Let's do the additive ones -- why not eh?
      }
      binary_polynomial scale(tm, wordSize, working.minimumTwoAddicValuationTerm(minimumTwoAddic(degree)));

      return working * scale;
    }
  }

  static binary_polynomial random(TermManager &tm, uint32_t wordSize, size_t degree) {
    binary_polynomial tmp(tm, wordSize);  // This is ugly, term operation should not be member functions
    std::vector<Term> coefficients;
    for (size_t i = 0; i <= degree; ++i) {
      coefficients.push_back(tmp.random());
    }
    return binary_polynomial(tm, wordSize, coefficients);
  }

  static binary_polynomial randomPermutationPolynomial(TermManager &tm, uint32_t wordSize, size_t degree) {
    binary_polynomial tmp(tm, wordSize);

    // Slow but unbiased
    do {
      tmp = random(tm, wordSize, degree);
    } while (tmp.isPermutationPolynomial() != TRUE);

    return tmp;
  }

  // yes -> 1, no -> 0, unknown -> -1
  int isPermutationPolynomial() const {
    if (degree() == 0) {
      return false;
    }

    // coeff[1] is odd
    int checkOne = simpleTermEqual(extractLSB(coeff[1]), extractLSB(constant(1u)));
    if (checkOne != TRUE) {
      return checkOne;
    }

    // sum of even coeff is even
    Term evenSum = constant(0u);
    for (size_t i = 2; i <= this->degree(); i += 2) {
      evenSum = add({evenSum, coeff[i]});
    }
    int checkTwo = simpleTermEqual(extractLSB(evenSum), extractLSB(constant(0u)));
    if (checkTwo != TRUE) {
      return checkTwo;
    }

    // sum of odd coeff is even
    Term oddSum = constant(0u);
    for (size_t i = 3; i <= this->degree(); i += 2) {
      oddSum = add({oddSum, coeff[i]});
    }
    int checkThree = simpleTermEqual(extractLSB(oddSum), extractLSB(constant(0u)));
    return checkThree;
  }
  
  
  // Performs a very basic evaluation of the polynomial
  Term eval(Term x) const {
    std::vector<Term> multiplied;
    Term power = constant(1u);

    for (size_t i = 0; i <= this->degree(); ++i) {
      //std::cout << i << " Power " << power << std::endl;

      Term multipliedTerm = rewriter::rewrite(mult({coeff[i], power}));
      //std::cout << i << " MultipliedTerm " << multipliedTerm << std::endl;
      
      multiplied.push_back(multipliedTerm);
      power = rewriter::rewrite(mult({power, x}));
    }

    Term result;
    if (multiplied.size() > 1) {
      result = add(multiplied);
    } else {
      result = multiplied[0];
    }

    #ifdef USE_BV
    return result;
    #else
    return mod({result, powerOfTwo(w)});
    #endif
  }

  // This is the brute force test
  bool valueEqual(const binary_polynomial &p) const {
    assert(w < 64);  // Not that you will want to wait for much past w = 20
    for (uint64_t i = 0; i < (1ull << w); ++i) {
      Term iTerm = constant(i);

      if (simpleTermEqual(this->eval(iTerm), p.eval(iTerm)) == 1) {
	continue;
      } else {
	return false;
      }
    }
    return true;
  }


  // For simplifying
  binary_polynomial substitute(const std::vector<Term> &from, const std::vector<Term> &to) const {
    std::vector<Term> subs;

    for (size_t i = 0; i <= this->degree(); ++i) {
      subs.push_back(rewriter::rewrite(this->coeff[i].substitute(from, to)));
    }

    return binary_polynomial(tm, w, subs);
  }
  
  // Compute the least significant bit of the output when evaluated with the term
  Term lsb(Term x) const {
    return extractLSB(eval(x));
  }

  
  
  // Remove trailing zeros
  void compact(void) {
    if (this->coeff.size() == 1) {
      return;
    }
    
    for (size_t i = this->coeff.size() - 1; i > 0; --i) {
      Term leading = this->coeff[i];
      if (simpleTermEqual(leading, constant(0u)) == 1) {
	  // Can remove the term
	  this->coeff.pop_back();
      } else {
	break;
      }
    }
    return;
  }

  binary_polynomial & operator= (const binary_polynomial &other) {
    assert(&this->tm == &other.tm); // Can't reassign tm, so check it is the same
    this->w = other.w;
    this->bv = other.bv;
    this->coeff = other.coeff;

    return (*this);
  }

  
  // Arithmetic
  binary_polynomial operator+ (const binary_polynomial &other) const {
    std::vector<Term> result;

    size_t longest = std::max(this->coeff.size(), other.coeff.size());
    for (size_t i = 0; i < longest; ++i) {
      if (i < this->coeff.size()) {
	if (i < other.coeff.size()) {
	  result.push_back(rewriter::rewrite(add({this->coeff[i], other.coeff[i]})));
	} else {
	  result.push_back(this->coeff[i]);
	}
      } else {
	assert(i < other.coeff.size());
	result.push_back(other.coeff[i]);
      }
    }
    
    return binary_polynomial(tm, w, result);
  }

  binary_polynomial operator- (const binary_polynomial &other) const {
    std::vector<Term> result;

    size_t longest = std::max(this->coeff.size(), other.coeff.size());
    for (size_t i = 0; i < longest; ++i) {
      if (i < this->coeff.size()) {
	if (i < other.coeff.size()) {
	  result.push_back(rewriter::rewrite(sub({this->coeff[i], other.coeff[i]})));
	} else {
	  result.push_back(this->coeff[i]);
	}
      } else {
	assert(i < other.coeff.size());
	result.push_back(rewriter::rewrite(neg({other.coeff[i]})));
      }
    }
    
    return binary_polynomial(tm, w, result);
  }

  binary_polynomial operator* (const binary_polynomial &other) const {
    std::vector<Term> result;

    size_t thisDegree = this->degree();
    size_t otherDegree = other.degree();

    for (size_t i = 0; i <= thisDegree + otherDegree; i++) {
      result.push_back(constant(0u));
    }

    for (size_t i = 0; i < this->coeff.size(); ++i) {
      for (size_t j = 0; j < other.coeff.size(); ++j) {
	result[i + j] = rewriter::rewrite(add({result[i + j], mult({this->coeff[i], other.coeff[j]})}));
      }
    }

    return binary_polynomial(tm, w, result);
  }

  size_t degree(void) const {
    return this->coeff.size() - 1;
  }

  // This is Arnau's reduction using factorial normal form
  //#define LOG_REDUCE 1
  binary_polynomial reduce (void) const {
    if (this->degree() <= 1) {
      return binary_polynomial(*this);
    } else {
      // We will need the factorial basis polynomials for up to the current degree
      // These are 1, x, x*(x-1), x*(x-1)*(x-2), ...
      std::vector<binary_polynomial> factorialBasis;
      factorialBasis.push_back(binary_polynomial(tm, w, constant(1u), 0));
      factorialBasis.push_back(binary_polynomial(tm, w, constant(1u), 1));
      for (size_t i = 2; i <= this->degree(); ++i) {
	binary_polynomial constTerm(tm, w, constant(i - 1));
	binary_polynomial xTerm(tm, w, constant(1u), 1);
	binary_polynomial factTerm = xTerm - constTerm;
	//binary_polynomial factTerm = xTerm + constTerm;  // Works, equivalent, easier to check by hand for BV
	factorialBasis.push_back(factorialBasis[i-1] * factTerm);
      }

      // Dump the basis polynomials
      #ifdef LOG_REDUCE
      for (size_t i = 0; i < factorialBasis.size(); ++i) {
	std::cout << i << "th basis : " << factorialBasis[i] << std::endl;
      }
      #endif

      // Now we need to convert *this into factorial normal form
      // Work from the highest degree down, subtracting a multiple of
      // the basis 
      binary_polynomial working(*this);
      binary_polynomial factorialNormalForm(tm, w);

      #ifdef LOG_REUDCE
      std::cout << working.degree() << " " << working << std::endl;
      #endif
      // Slightly wonky loop condition as we want to execute for 0 and size_t is unsigned
      size_t start = working.degree();
      for (size_t i = start; i <= start; --i) {
	if (i <= working.degree()) {
	  Term leadingCoefficient = working.coeff[i];
	  binary_polynomial basisMultiple = factorialBasis[i] * binary_polynomial(tm, w, leadingCoefficient);
	  working = working - basisMultiple;
	  factorialNormalForm = factorialNormalForm + binary_polynomial(tm, w, leadingCoefficient, i);
#ifdef LOG_REDUCE
	  std::cout << working.degree() << " " << working << std::endl;
#endif
	} else {
	  // Skip?
	}
      }

      #ifdef LOG_REDUCE
      std::cout << "In factorial normal form -- " << factorialNormalForm.degree() << " " << factorialNormalForm << std::endl;
      #endif
      
      // Modulo reduction
      // In factorial normal form we have a lower bound on the 2-addic
      // valuation of any monomial.  For example x*(x-1) will always have
      // a 2-addic valuation of at least 1 as one of x and x-1 will be even!
      // x^{(4)} = x*(x-1)*(x-2)*(x-3) will have a 2-addic valuation of 3
      // because at least two of them will be even and one will be a multiple
      // of four.  We can use this to reduce the coefficients.
      for (size_t i = 0; i <= factorialNormalForm.degree(); ++i) {

	// Compute the minimum 2-addic valuation
	size_t minimumTwoAddicVal = minimumTwoAddic(i);

	// Create m = 2^{w-minimumTwoAddicVal)
	Term m = working.minimumTwoAddicValuationTerm(minimumTwoAddicVal);

	// Reduce the coefficient modulo m
	factorialNormalForm.coeff[i] = mod({factorialNormalForm.coeff[i], m});
      }

      #ifdef LOG_REDUCE
      std::cout << "In reduced factorial normal form -- " << factorialNormalForm.degree() << " " << factorialNormalForm << std::endl;
      #endif

      
      // Put back into normal form
      // This is another basis transform
      binary_polynomial result(tm, w);
      for (size_t i = 0; i <= factorialNormalForm.degree(); ++i) {
	Term c = factorialNormalForm.coeff[i];
	binary_polynomial res = factorialBasis[i] * binary_polynomial(tm, w, c);
	result = result + res;
      }
      
      return result;
    }
  }

  binary_polynomial subpolynomial(Term b) {
    // This is a basis change to 2y + b where b \in {0,1}
    // We will do it by converting cx^n to c*(2y+1)^n
    binary_polynomial working(tm, w, constant(1u));
    binary_polynomial multiplier(tm, w, {1u, 2u});
    
    // The first term is split out as the "pure y" term.
    // We accumulate the pure y and the b terms separately and join at the end.
    binary_polynomial pureY(tm, w); // Zero
    binary_polynomial mixedB(tm, w); // Zero
    
#ifdef USE_BV
    Term z = tm.mkConst(bv, "z");
#else
    Term z = tm.mkConst(tm.getIntegerSort(), "z");
#endif

    for (size_t i = 0; i <= this->degree(); ++i) {
      // std::cout << i << " working : " << working << std::endl;
      
      binary_polynomial tmp = binary_polynomial(tm, w, this->coeff[i]) * working;
      binary_polynomial leadingMonomial = (tmp.degree() < i) ? binary_polynomial(tm, w): binary_polynomial(tm, w, tmp.coeff[tmp.degree()], tmp.degree());
      tmp = tmp - leadingMonomial;

      // std::cout << i << " tmp : " << tmp << std::endl;
      // std::cout << i << " leadingMonomial : " << leadingMonomial << std::endl;
      
      // Accumulate
      pureY = pureY + leadingMonomial;
      mixedB = mixedB + tmp;

      // std::cout << i << " pureY : " << pureY << std::endl;
      // std::cout << i << " mixedB : " << mixedB << std::endl;
      
      // Iterate
      working = working * multiplier;
    }

    // Finally put together the pure y and the b terms
    std::vector<Term> res;

    size_t limit = std::max(pureY.degree(), mixedB.degree());
    for (size_t i = 0; i <= limit; ++i) {
      Term yTerm = (i <= pureY.degree()) ? pureY.coeff[i] : constant(0u);
      Term bTerm = (i <= mixedB.degree()) ? mixedB.coeff[i] : constant(0u);

      // !!!Caution!!! Stupid magic...
      res.push_back(add({yTerm, ite({b, bTerm, constant(0u)})}));
      //res.push_back(ite({b, add({yTerm, bTerm}), yTerm}));
    }

    return binary_polynomial(tm,w,res);
  }

  // Extract a polynomial that computes the top w-1 bits.
  // Dividing each coefficient by 2 (rounding down) is sufficient
  // but there is also scope for further simplification.
  // MUST be run on a subpolynomial!
  // Otherwise you will need a correction term
  binary_polynomial topBits() const {
    assert(w > 1);
    std::vector<Term> divided;

    for (size_t i = 0; i <= this->degree(); ++i) {
      divided.push_back(extractTopBits(this->coeff[i]));
    }

    return binary_polynomial(tm, w-1, divided);
  }


  // The complete subpolynomial encoding of a polynomial
  Term encode(Term x) const {
    binary_polynomial working(*this);
    Term var = x;
    std::vector<Term> output;

    if (working.degree() == 0) {
      return working.coeff[0];
    }

    // When the subpolynomials become linear, at or before w/2, encode them directly
    bool linearShortCut = true;
    
    for (uint32_t i = 0; i < w; ++i) {
      // Handle the simple cases
      if (linearShortCut && working.degree() <= 1) {
	output.push_back(tm.mkTerm(Kind::BITVECTOR_ADD, { tm.mkTerm(Kind::BITVECTOR_MULT, { working.coeff[1], var}), working.coeff[0]}));
	break;
      }

      
      // The output bit
      output.push_back(working.lsb(var));

      // An actual example of a split while loop!
      if (i + 1u == w) {
	break;
      }

      // Now let's start on the subpolynomial step
      Term lsbInput = working.extractLSB(var);
    
#ifdef USE_BV
      Term bit = lsbInput;
#else
      Term bit = tm.mkTerm(Kind::EQUAL, {lsbInput, constant(1)});
#endif
      binary_polynomial sub = working.subpolynomial(bit);
      
      // Now get the top bits
      binary_polynomial subDiv2 = sub.topBits();

      // On to the next iteration
      var = working.extractTopBits(var);
      working = subDiv2;
    }

    // So we concatinate in the right order
    std::reverse(output.begin(), output.end());

    return tm.mkTerm(Kind::BITVECTOR_CONCAT, output);
  }
  

  
  friend std::ostream & operator<<(std::ostream &out, const binary_polynomial &p);
  
 protected :
  TermManager &tm;
  uint32_t w;
  Sort bv;
  std::vector<Term> coeff;
};

// A semi-infix represetation :-|
std::ostream & operator<<(std::ostream &out, const binary_polynomial &p) {
  for (size_t i = 0; i <= p.degree(); ++i) {
    out << "[ " << p.coeff[i] << " ]";
    if (i > 0) {
      out << " x^" << i;
    }
    if (i < p.degree()) {
      out << " + ";
    }
  }
  return out;
}

#endif

