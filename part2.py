"""
=============================================================
CS143-15 Coursework: Part Two
=============================================================

Complete Part Two of the coursework here! 

NOTE: coursework1.py and coursework2.py are the only files 
you should edit (excluding interpreter.py for changing the
target coursework file or default input string)

Entry point:
    main(...) called from interpreter.py

Preamble

1. Soundness
The proof system is sound because it builds off the foundation of sound inference rules, and building specialisations or compund formulas from these inference 
rules leads to sound proof systems. In addition to this I have implemented the correct syntax for each sound inference rule therefore in practice the 
inference rule is sound, for example IMP_ELIM checks that the antecedent matches the implication, and NOT_ELIM verifies that one formula is the negation of 
the other before deriving a contradiction. Additionally, scope handling ensures that formulas derived under assumptions are limited to their specific scope 
and therefore can only be accessed in their valid contexts, this prevents invalid conclusions from being derived preserving logical corectness.

2. Completeness
The system is not complete for full propositional logic because NDLmini only implements a small proportion of propositional logic, for example formulas are 
flat rather than arbitrarily nested, assumptoions are restricted to literals, and some standard features such as double negation aren't explicitly included. 
Consquently there are valid propositional arguments and tautologies that cannot be written in this language, which are expressible in propositional logic 
which makes the validator incomplete.

3. Improvements
The validator could be improved by enhancing error reporting, for example by distinguishing between syntax and logic errors more clearly and stopping goal
evaluation when parsing fails. For example syntax errors could occur and therefore the input is rejected, but the goal could be sucuessfully derived in
parallel as a consquent of it being derived in the global scope. Additionally, the language could be extended to supprort more advanced inference rules 
such as proof by contradiction, and other additional rules to create a complete system (such as the eight axioms visited in lectures). Furthermore richer 
strcutures such as compunds propositional statements could be implemented to broaden the langauge of NDLmini.

"""

from pushdown import *
from tokens import *
from logic import *
from parser_utils import *

# Initialise a new PDA 
my_automaton: PushdownAutomaton = PushdownAutomaton()

# Declaring and initialising global variables for handling proof logic
goal: Formula = Formula()
premises: set[Formula] = set()
derived:  set[Formula] = set()
assumptions: dict[tuple[Literal, ...], set[Formula]] = {}

def add_derivation(f: Formula):
    """
    Adds a formula to the current scope
    :param f: Formula to be added
    """
    scope: tuple[Literal, ...] = tuple(my_automaton.get_stack())    # Store current scope in the tuple

    # If no assumptions store in derived set 
    if len(scope) == 0:
        derived.add(f)
    else:
        if scope not in assumptions:
            assumptions[scope] = set()
        assumptions[scope].add(f)

def is_in_scope(f: Formula, scope_list: list[Literal] = []) -> bool :
    """
    Checks if a specified formula is in scope
    :param f: Formula to check 
    :return: True if the formula was found
    """
    if len(scope_list) == 0:
        scope_list = my_automaton.get_stack()
    
    # Check global scope first 
    if f in (premises | derived):
        return True
    
    # Check current scope and all parent scopes
    for i in range(1, len(scope_list) + 1):
        scope = tuple(scope_list[:i])
        if scope in assumptions and f in assumptions[scope]:
            return True
    return False

def apply_and_intro(f_L: Formula, f_R: Formula) -> Formula:
    # Checks if both formuals are binary
    if f_L.is_binary or f_R.is_binary:
        raise LogicalError("AND_INTRO requires two unary formulas")
    
    # Attempt to convert both formulas to literals
    lit_L: Literal = f_L.to_literal()
    lit_R: Literal = f_R.to_literal()

    # Check if both conjuncts are in scope
    if not is_in_scope(f_L) or not is_in_scope(f_R):
        raise LogicalError(f"AND_INTRO: Both conjuncts [{f_L}, {f_R}] must be in scope.")
    
    # Return the conjunction of the two literals
    return Formula(lit_L, TOKENS.AND, lit_R)

def apply_and_elim(f_L: Formula, f_R: Formula) -> Formula:
    # Check whether if one of the functions is a conjunction
    if f_L.is_binary and f_L.op == TOKENS.AND:
        conjunction = f_L
        other = f_R
    elif f_R.is_binary and f_R.op == TOKENS.AND:
        conjunction = f_R
        other = f_L
    else:
        raise LogicalError("AND_ELIM requires one input to be a conjunction")
    
    # Check the conjunction is in scope
    if not is_in_scope(conjunction):
        raise LogicalError(f"AND_ELIM: Conjunction [{conjunction}] must be in scope")
    
    # Verify that the other formula is binary
    if other.is_binary:
        raise LogicalError("AND_ELIM requires the one input to be unary")
    
    other_lit: Literal = other.to_literal()
    # Verify that it mathces one of the conducts
    if other_lit != conjunction.lit_L and other_lit != conjunction.lit_R:
        raise LogicalError(f"AND_ELIM: [{other}] is not a conjunct of [{conjunction}]")
    
    # Return the other conjuct
    if other_lit == conjunction.lit_L:
        return Formula(conjunction.lit_R)
    else:
        return Formula(conjunction.lit_L)
    
def apply_or_intro(f_L: Formula, f_R: Formula) -> Formula:
    # Both inputs must be unary 
    if f_L.is_binary or f_R.is_binary:
        raise LogicalError("OR_INTRO requires two unary formulas")
    
    lit_L: Literal = f_L.to_literal()
    lit_R: Literal = f_R.to_literal()

    # At least one disjunct must be in the scope
    if not is_in_scope(f_L) and not is_in_scope(f_R):
        raise LogicalError(f"OR_INTRO requires at least one of [{f_L}, {f_R}] must be in scope")
    
    return Formula(lit_L, TOKENS.OR, lit_R)

def apply_or_elim(f_L: Formula, f_R: Formula) -> Formula:
    # Check whether if one of the functions is a conjunction
    if f_L.is_binary and f_L.op == TOKENS.OR:
        disjunction = f_L
        other = f_R
    elif f_R.is_binary and f_R.op == TOKENS.OR:
        disjunction = f_R
        other = f_L
    else:
        raise LogicalError("OR_ELIM requires one input to be a disjunction")
    
    # Check if both are in the scope
    if not is_in_scope(disjunction) or not is_in_scope(other):
        raise LogicalError(f"OR_ELIM requires both [{disjunction}] and [{other}] must be in scope")
    
    # Check if one input is unary
    if other.is_binary:
        raise LogicalError("OR_ELIM requires one input to be unary")
    
    other_lit: Literal = other.to_literal()
    # Make sure literal is negated
    if not other_lit.is_neg:
        raise LogicalError("OR_ELIM requires one input to be negated")
    
    negated_base: Literal = other_lit.get_negation()
    # Make sure negated literal appers in the disjunction
    if negated_base != disjunction.lit_L and negated_base != disjunction.lit_R:
        raise LogicalError(f"OR_ELIM error because [{other}] is not the negation of a disjunct in [{disjunction}] ")
    
    # Return the correct literal
    if negated_base == disjunction.lit_L:
        return Formula(disjunction.lit_R)
    else:
        return Formula(disjunction.lit_L)
    
def apply_imp_intro(f_L: Formula, f_R: Formula) -> Formula:
    # Check if both formulas are unary
    if f_L.is_binary or f_R.is_binary:
        raise LogicalError("IMP_INTRO requires two unary formulas")
    
    lit_L: Literal = f_L.to_literal()
    lit_R: Literal = f_R.to_literal()

    # If consquent in the global scope
    if f_R in (premises | derived):
        return Formula(lit_L, TOKENS.IMP, lit_R)
    
    # Consquent available in child scope of antecendent
    for scope in assumptions:
        formulas = assumptions[scope]
        if f_R in formulas and is_in_scope(f_L, list(scope)):
            return Formula(lit_L, TOKENS.IMP, lit_R)
    raise LogicalError(f"IMP_INTRO means [{f_R}] must be derivable in a scope where [{f_L}] is assumed")
    
def apply_imp_elim(f_L: Formula, f_R: Formula) -> Formula:
    # Identify which input is the implication and which is the antecendent
    if f_L.is_binary and f_L.op == TOKENS.IMP:
        implication = f_L
        antecedent_formula = f_R
    elif f_R.is_binary and f_R.op == TOKENS.IMP:
        implication = f_R
        antecedent_formula = f_L
    else:
        raise LogicalError("IMP_ELIM requires one input to be a implication")
    
    # Check if both are in the scope
    if not is_in_scope(implication) or not is_in_scope(antecedent_formula):
        raise LogicalError(f"IMP_ELIM requires both [{implication}] and [{antecedent_formula}] to be in scope")
    
    # The antecedent input must be unary
    if antecedent_formula.is_binary:
        raise LogicalError("IMP_ELIM requires the antecedent input to be unary")
    
    antecedent_lit: Literal = antecedent_formula.to_literal()
    # Check if antecendent is unary
    if antecedent_lit != implication.lit_L:
        raise LogicalError(f"for IMP_ELIM [{antecedent_formula}] is not the antecedent of [{implication}]")
    
    return Formula(implication.lit_R)

def apply_not_elim(f_L: Formula, f_R: Formula) -> Formula:
    # Both inputs must be unary formulas
    if f_L.is_binary or f_R.is_binary:
        raise LogicalError("NOT_ELIM requires two unary formulas")
    
    lit_L: Literal = f_L.to_literal()
    lit_R: Literal = f_R.to_literal()

    # Both formulas must be in the scope 
    if not is_in_scope(f_L) or not is_in_scope(f_R):
        raise LogicalError(f"NOT_ELIM requires both [{f_L}] and [{f_R}] to be in the scope")
    
    # One literal must be the negation of the other
    if lit_L != lit_R.get_negation() and lit_R != lit_L.get_negation():
        raise LogicalError(f"NOT_ELIM requires one formula to be the negation of the other: [{f_L}], [{f_R}]")
    
    return Contradiction() # Return the contradiction

def apply_not_intro(f_L: Formula, f_R: Formula) -> Formula:
    # Both inputs must be unary formulas
    if f_L.is_binary or f_R.is_binary:
        raise LogicalError("NOT_INTRO requires two unary formulas")
    
    lit_L: Literal = f_L.to_literal()
    lit_R: Literal = f_R.to_literal()

    # Both inputs must be the same
    if lit_L != lit_R:
        raise LogicalError("NOT_INTRO requires two matching inputs")
    
    for scope in assumptions:
        formulas = assumptions[scope]
        if Contradiction() in formulas and is_in_scope(f_L, list(scope)):
            return Formula(lit_L.get_negation())
    raise LogicalError(f"NOT_INTRO requires contradiction to be derivable in a scope where [{f_L}] is assumed")

def main(stream: TokenStream):
    """
    Entry point, takes an input stream and inputs it to the automaton
    :param stream: TokenStream to parse
    """
    my_automaton.set_start_state(Q_START())
    my_automaton.set_accept_state(Q_ACCEPT())

    is_accepted = my_automaton.parse(stream)

    if is_accepted:
        print(f"The input [{stream}] is ACCEPTED.")
    else:
        print(f"The input [{stream}] is REJECTED.")

    # Print the result of logical verification
    if is_in_scope(goal):
        print(f"The goal {goal} was SUCCESSFULLY derived.")
    else:
        print(f"The goal {goal} was NOT derived.")

"""
====================== State Definitions ======================
Placeholder - copy and paste your States over from Coursework1.py
"""

# TODO : Copy and paste your states here!
class Q_START(State):
    def step(self, stream: TokenStream) -> State:
        """
        Initial state - transition functions: 
            δ(Q_START, GIVEN) = Q_PREMISES
            δ(Q_START, DERIVE) = Q_GOAL
        """
        next_tok: Token = stream.next() # Consume next token

        if (next_tok == TOKENS.GIVEN):
            return Q_PREMISES()
        elif (next_tok == TOKENS.DERIVE):
            return Q_GOAL()
        else:
            raise SyntaxError("Expected GIVEN or DERIVE therfore token not recognised")


class Q_ACCEPT(State):  
    def step(self, stream: TokenStream) -> State:
        """
        There are no transitions out of this state
        :raise AutomatonSyntaxError: If there are any remaining symbols 
        """
        if not stream.is_eof():  # Tokens still remain in the stream
            raise AutomatonSyntaxError(
                    "End of Input", str(self), stream.next()  # Expected End of Input in Q_ACCEPT
                )  
        return self  # Safety net - should be unreachable

class Q_PREMISES(State):
    def step(self, stream: TokenStream) -> State:
        """
        Transition function:
            δ(Q_PREMISES, <formula>) = Q_START
        """
        formula = consume_formula(stream) # Consume <formula>
        print(f"Adding premise: {formula}")
        premises.add(formula) # Add the formula to premises
        return Q_START() # Transition to Q_START
    
class Q_GOAL(State):
    def step(self, stream: TokenStream) -> State:
        """
        Transition function: 
            δ(Q_GOAL, <formula>) = Q_PROOF
        """
        formula = consume_formula(stream)
        
        print(f"Setting goal: {formula}")
        
        global goal
        goal = formula

        return Q_PROOF()
    

class Q_PROOF(State):
    def step(self, stream: TokenStream) -> State:
        """
        Transition function:
            δ(Q_PROOF, CONCLUDE) = Q_ACCEPT
            δ(Q_PROOF, APPLY) = Q_INFERENCE
            δ(Q_PROOF, ASSUME) = Q_SUBPROOF_OPEN
            δ(Q_PROOF, END) = Q_PROOF; pop(<lit>)
        """
        next_tok: Token = stream.next() # Consume next token

        if (next_tok == TOKENS.CONCLUDE):
            return Q_ACCEPT()
        elif (next_tok == TOKENS.APPLY):
            return Q_INFERENCE()
        elif (next_tok == TOKENS.ASSUME):
            return Q_SUBPROOF_OPEN()
        elif(next_tok == TOKENS.END):
            my_automaton.pop()
            return Q_PROOF()
        else:
            raise SyntaxError("Expected CONCLUDE, APPLY, ASSUME or END therefore token not recognised")

class Q_INFERENCE(State):
    def step(self, stream: TokenStream) -> State:
        """
        Transition function:
        δ(Q_INFERENCE, <inference-rule> <formula> COMMA <formula>) = Q_PROOF 
        """
        inf_rule: Token = stream.next() # Consume the inference rule token

        if inf_rule.is_one_of(TOKENS.INF_RULES):
              
            formula_L: Formula = consume_formula(stream) # first formula (left)

            comma_tok: Token = stream.next()    # Comma token
            if comma_tok != TOKENS.COMMA:
                raise SyntaxError("Comma expected in the rule application")
            
            formula_R: Formula = consume_formula(stream) # second formula (right)
            
            formula_yield: Formula
            if inf_rule == TOKENS.AND_INTRO:
                formula_yield = apply_and_intro(formula_L, formula_R)
            elif inf_rule == TOKENS.AND_ELIM:
                formula_yield = apply_and_elim(formula_L, formula_R)
            elif inf_rule == TOKENS.OR_INTRO:
                formula_yield = apply_or_intro(formula_L, formula_R)
            elif inf_rule == TOKENS.OR_ELIM:
                formula_yield = apply_or_elim(formula_L, formula_R)
            elif inf_rule == TOKENS.IMP_INTRO:
                formula_yield = apply_imp_intro(formula_L, formula_R)
            elif inf_rule == TOKENS.IMP_ELIM:
                formula_yield = apply_imp_elim(formula_L, formula_R)
            elif inf_rule == TOKENS.NOT_INTRO:
                formula_yield = apply_not_intro(formula_L, formula_R)
            elif inf_rule == TOKENS.NOT_ELIM:
                formula_yield = apply_not_elim(formula_L, formula_R)
            else: 
                raise LogicalError(f"Unaccounted inference rule: {inf_rule}")

            print(f"{inf_rule} yield: {formula_yield}")
            add_derivation(formula_yield)
            return Q_PROOF()
        
        else:
            raise SyntaxError("Inference rule expected therefore rule not recognised")
        
class Q_SUBPROOF_OPEN(State):
    def step(self, stream: TokenStream) -> State:
        """
        Transition function:
        δ(Q_SUBPROOF_OPEN, <lit>) = Q_PROOF; push(<lit>)
        """
        lit: Literal = consume_lit(stream)  # read the literal onto the stack
        my_automaton.push(lit)  # push it onto the stack
        
        scope: tuple[Literal, ...] = tuple(my_automaton.get_stack())    # Store current scope in the tuple
        # Create storage for formulas subproof scope
        if scope not in assumptions:
            assumptions[scope] = {Formula(lit)}

        print(f"Entering scope: {[str(lit) for lit in scope]}")

        return Q_PROOF()
    