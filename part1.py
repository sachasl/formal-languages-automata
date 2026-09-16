"""
=============================================================
CS143-15 Coursework: Part One
=============================================================

Complete Part One of the coursework here! 

NOTE: coursework1.py and coursework2.py are the only files 
you should edit (excluding interpreter.py for changing the
target coursework file or default input string)

Entry point:
    main(...) called from interpreter.py

Preamble
Each state subclass represents one state in the PDA, and the step() function implements the partial delta transition function by consuming the 
next token and returning exactly one next state, or raising a SyntaxError if there isn't a valid transition that can occur. Therfore this makes 
the automoton deterministic because there is at most one valid move that can be made from a given state.

The different control states reflect the structure of the language: Q_START handles GIVEN and DERIVE from the start state; Q_PREMISES and Q_GOAL consume 
formulas; Q_PROOF handles keywords APPLY, ASSUME, END and CONCLUDE, Q_INFERENCE parses inference-rule applications; and Q_SUBPROOF_OPEN reads a literal 
after the keyword ASSUME. The stack is utlised for nested subproofs only where ASSUME pushes a literal onto the stack and END pops it accordingly,
therfore because acceptance requires both reading Q_ACCEPT and having an empty stack this approach handles the context-free structure of nested scopes
in NDLmini.

I chose this design because it keeps parsing logic local to each state, so that the syntax is easy to trace against the according PDA diagram, therfore
invalid syntax is simple to identify.

"""

from pushdown import *      # State and PDA base classes
from tokens import *        # TOKENS, Token, TokenStream
from logic import *         # Literal, Formula, Contradiction
from parser_utils import *  # Parsing error and traversal helpers

# Initialise a new PDA 
my_automaton: PushdownAutomaton = PushdownAutomaton()

def main(stream: TokenStream):
    """
    Entry point, takes an input stream and inputs it to the automaton
    :param stream: TokenStream to parse
    """
    # Assign start state Q_START and accept state Q_ACCEPT 
    my_automaton.set_start_state(Q_START())
    my_automaton.set_accept_state(Q_ACCEPT())

    # Parse the input stream using the PDA
    is_accepted = my_automaton.parse(stream)

    # Print the result
    if is_accepted:
        print(f"The input [{stream}] is ACCEPTED.")
    else:
        print(f"The input [{stream}] is REJECTED.")

"""
====================== State Definitions ======================
"""

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
        consume_formula(stream) # Consume next formula or raise SyntaxError automatically
        return Q_START()
    
class Q_GOAL(State):
    def step(self, stream: TokenStream) -> State:
        """
        Transition function: 
            δ(Q_GOAL, <formula>) = Q_PROOF
        """
        consume_formula(stream)
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
        next_tok: Token = stream.next() # Consume the inference rule token

        if next_tok.is_one_of(TOKENS.INF_RULES):
            consume_formula(stream) # first formula

            comma_tok: Token = stream.next()    # Comma token
            if comma_tok != TOKENS.COMMA:
                raise SyntaxError("Comma expected in the rule application")
            
            consume_formula(stream) # second formula
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
        return Q_PROOF()