/*
** rewriter.h
**
** Martin Brain
** martin.brain@citystgeorges.ac.uk
** 07/03/25
**
** I want a global, stateless rewriter.
** cvc5's rewriter is accessible via a solver object.
** So we are going to do some dirty hacks...
**
*/

#include <cassert>
#include <memory>
#include <iostream>

#include <cvc5/cvc5.h>


#ifndef REWRITER_H
#define REWRITER_H

using namespace cvc5;

class rewriter {
 protected :
  static std::shared_ptr<Solver> slv;

 public :
  static void setRewriterSolver (std::shared_ptr<Solver> s) {
    slv = s;
    return;
  }

  static Term rewrite(Term t) {
    Term res = slv->simplify(t);
    
    if (t.getKind() == Kind::BITVECTOR_EXTRACT) {
      assert(t.hasOp());
      Op extractParam = t.getOp();

      assert(extractParam.getNumIndices() == 2);
      Term upper = extractParam[0];
      Term lower = extractParam[1];
      assert(upper.isUInt32Value());
      assert(lower.isUInt32Value());
      
      uint32_t u = upper.getUInt32Value();
      uint32_t l = lower.getUInt32Value();

      assert(t.getNumChildren() == 1);
      Term child = t[0];
      Kind childKind = child.getKind();
      Sort s = t.getSort();
      assert(s.isBitVector());
      uint32_t width = s.getBitVectorSize();  // Be careful, this is child size, not extract size

      TermManager &tm = slv->getTermManager();
      Op lsbOp = tm.mkOp(Kind::BITVECTOR_EXTRACT, {0,0});
      
      if (childKind == Kind::ITE) {
	// Rewrite both sides
	// Yes, this is risky but we build them with a constant on one side
	Term cond = child[0];
	Term left = rewriter::rewrite(tm.mkTerm(extractParam, {child[1]}));
	Term right = rewriter::rewrite(tm.mkTerm(extractParam, {child[2]}));
	
	res = rewriter::rewrite(tm.mkTerm(Kind::ITE, { cond, left, right }));
	
      } else if (u == 0 && l == 0) {
	//std::cout << "Found lsb " << t << std::endl;

	// Can push the lsb down through t-functions
	if (childKind == Kind::BITVECTOR_ADD || childKind == Kind::BITVECTOR_MULT) {
	  
	  std::vector<Term> sub;
	  for (size_t i = 0; i < child.getNumChildren(); ++i) {
	    sub.push_back(rewriter::rewrite(tm.mkTerm(lsbOp, {child[i]})));
	  }
	  res = rewriter::rewrite(tm.mkTerm((childKind == Kind::BITVECTOR_ADD) ? Kind::BITVECTOR_XOR : Kind::BITVECTOR_AND, sub));
	}
	// lsb on other things
	
      } else if (u == width && l == 1) {
	//std::cout << "Found topBits " << t << std::endl;
	
	if (childKind == Kind::BITVECTOR_ADD) {
	  // Can simplify if all but one the args as a LSB that is zero
	  // For now let's just do binary
	  if (child.getNumChildren() == 2) {    
	    // This is a somewhat fiddly rewrite...
	    
	    // We need to extract the rest of both children
	    Term restc0 = rewriter::rewrite(tm.mkTerm(extractParam, {child[0]}));
	    Term restc1 = rewriter::rewrite(tm.mkTerm(extractParam, {child[1]}));
	    //std::cout << "Rewriting" << std::endl;
	    //std::cout << restc0 << std::endl;
	    //std::cout << restc1 << std::endl;
	    
	    // We also need to LSB them
	    Term lsbc0 = rewriter::rewrite(tm.mkTerm(lsbOp, {child[0]}));
	    Term lsbc1 = rewriter::rewrite(tm.mkTerm(lsbOp, {child[1]}));

	    //std::cout << tm.mkTerm(lsbOp, {child[1]}) << std::endl;
	    //std::cout << lsbc0 << std::endl;
	    //std::cout << lsbc1 << std::endl;
	    //std::cout << std::endl;
	    
	    // And together the two lsbs and extend!
	    Term lsbAnd = rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_AND, {lsbc0, lsbc1}));
	    Term extended = rewriter::rewrite(tm.mkTerm(tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {width-1}), {lsbAnd}));

	    //std::cout << extended << std::endl;
	    
	    // Finally add them all up!
	    res = rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_ADD, { restc0, restc1, extended }));
	    
	  } else {
	    std::vector<Term> sub;
	    std::vector<Term> bits;

	    for (size_t i = 0; i < child.getNumChildren(); ++i) {
	      sub.push_back(rewriter::rewrite(tm.mkTerm(extractParam, {child[i]})));
	      bits.push_back(rewriter::rewrite(tm.mkTerm(tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {width}), {rewriter::rewrite(tm.mkTerm(lsbOp, {child[i]}))})));
	    }
	    // Don't rewrite to avoid recursion
	    sub.push_back(/*rewriter::rewrite*/(tm.mkTerm(extractParam, {rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_ADD,bits))})));
	    res = rewriter::rewrite(tm.mkTerm(Kind::BITVECTOR_ADD, sub));
	  }
	}
	// rest on things other than add
	
      } else {
      	std::cout << "Found other extract " << t << std::endl;
	
      }

    }
    // Other kinds go here
    
    /*
    if (t.getKind() == Kind::INTS_DIVISION &&
	t[0].getKind() == Kind::ADD &&
	t[1].isIntegerValue()) {
      // This is unsafe in the general case as it can create divide by zero issues
      // However as we know that 
    }
    */
    
    return res;
  }
};

#endif

