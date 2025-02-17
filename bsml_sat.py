import clingo

from abc import ABC, abstractmethod

from gcc import solve_gcc

class BSMLFormula(ABC):

    @abstractmethod
    def __repr__(self):
        pass


class Var(BSMLFormula):

    def __init__(self, name):
        self.name = name
        self.op_name = "Var"

    def __repr__(self):
        return self.op_name + "(" + str(self.name) + ")"


class NE(BSMLFormula):

    def __init__(self):
        pass

    def __repr__(self):
        return "NE"


class Bottom(BSMLFormula):

    def __init__(self):
        pass

    def __repr__(self):
        return "⊥"


class Diamond(BSMLFormula):

    def __init__(self, child):
        self.child = child
        self.op_name = "<>"

    def __repr__(self):
        return self.op_name + "(" + self.child.__repr__() + ")"


class Box(BSMLFormula):

    def __init__(self, child):
        self.child = child
        self.op_name = "[]"

    def __repr__(self):
        return self.op_name + "(" + self.child.__repr__() + ")"


# class Empty(BSMLFormula):
#
#     def __init__(self, child):
#         self.child = child
#         self.op_name = "Empty"
#
#     def __repr__(self):
#         return self.op_name + "(" + self.child.__repr__() + ")"


class And(BSMLFormula):

    def __init__(self, *args):
        self.children = args
        self.op_name = "And"

    def __repr__(self):
        if not self.children:
            return self.op_name + "()"
        else:
            ch_reprs = map(lambda x: x.__repr__(), self.children)
            return self.op_name + "(" + ",".join(ch_reprs) + ")"


# class GOr(BSMLFormula):
#
#     def __init__(self, *args):
#         self.children = args
#         self.op_name = "GOr"
#
#     def __repr__(self):
#         if not self.children:
#             return self.op_name + "()"
#         else:
#             ch_reprs = map(lambda x: x.__repr__(), self.children)
#             return self.op_name + "(" + ",".join(ch_reprs) + ")"


class Or(BSMLFormula):

    def __init__(self, *args):
        self.children = args
        self.op_name = "Or"

    def __repr__(self):
        if not self.children:
            return self.op_name + "()"
        else:
            ch_reprs = map(lambda x: x.__repr__(), self.children)
            return self.op_name + "(" + ",".join(ch_reprs) + ")"


class Neg(BSMLFormula):

    def __init__(self, child):
        self.child = child
        self.op_name = "Neg"

    def __repr__(self):
        return self.op_name + "(" + self.child.__repr__() + ")"


def formula_to_nf(formula):
    # recursively replace Box by Neg-Diamond-Neg
    if not isinstance(formula, BSMLFormula):
        return None
    if isinstance(formula, (Var, NE, Bottom)):
        return formula
    if isinstance(formula, Neg):
        return Neg(formula_to_nf(formula.child))
    if isinstance(formula, Or):
        new_children = list(map(formula_to_nf, formula.children))
        return Or(*new_children)
    if isinstance(formula, And):
        new_children = list(map(formula_to_nf, formula.children))
        return And(*new_children)
    if isinstance(formula, Diamond):
        return Diamond(formula_to_nf(formula.child))
    if isinstance(formula, Box):
        return Neg(Diamond(Neg(formula_to_nf(formula.child))))


def enrich_formula(formula):
    if not isinstance(formula, BSMLFormula):
        return None
    if isinstance(formula, Var):
        return And(formula, NE())
    if isinstance(formula, Neg):
        return And(Neg(enrich_formula(formula.child)),NE())
    if isinstance(formula, And):
        enriched_children = map(enrich_formula, formula.children)
        return And(*enriched_children, NE())
    if isinstance(formula, Or):
        enriched_children = map(enrich_formula, formula.children)
        return And(Or(*enriched_children), NE())
    if isinstance(formula, Diamond):
        return And(Diamond(enrich_formula(formula.child)), NE())
    if isinstance(formula, Box):
        return enrich_formula(Neg(Diamond(Neg(formula.child))))
    if isinstance(formula, Bottom):
        return formula


def encode_formula_tree(formula, num_vars, polarity):

    def encode_formula_tree(index, formula, num_vars, polarity):

        posneg = "neg"
        if polarity:
            posneg = "pos"

        # Case: variable
        if isinstance(formula, Var):
            return index+1, f"ft_node({index},var({formula.name}),{posneg}).\n"
        # Case: NE
        if isinstance(formula, NE):
            return index+1, f"ft_node({index},ne,{posneg}).\n"
        # Case: bottom
        if isinstance(formula, Bottom):
            return index+1, f"ft_node({index},bottom,{posneg}).\n"
        # Case: negation
        if isinstance(formula, Neg):
            program = f"ft_node({index},neg,{posneg}).\n"
            program += f"ft_edge({index},{index+1},equal).\n"
            index, add_program = encode_formula_tree(
                index+1,
                formula.child,
                num_vars,
                not polarity,
            )
            program = add_program + program
            return index, program
        # Case: conjunction/disjunction
        if isinstance(formula, (And, Or)):
            orig_index = index
            index += 1
            program = ""
            child_indices = []
            for child in formula.children:
                child_indices.append(index)
                index, add_program = encode_formula_tree(
                    index,
                    child,
                    num_vars,
                    polarity,
                )
                program = add_program + program
            if isinstance(formula, Or):
                program += f"ft_node({orig_index},or,{posneg}).\n"
            if isinstance(formula, And):
                program += f"ft_node({orig_index},and,{posneg}).\n"
            edge_type = "equal"
            if ((isinstance(formula, And) and not polarity) or \
                (isinstance(formula, Or) and polarity)):
                edge_type = "join"
            for child_index in child_indices:
                program += f"ft_edge({orig_index},{child_index},{edge_type}).\n"
            return index, program
        # Case: diamond/box
        if isinstance(formula, (Diamond, Box)):
            orig_index = index
            index += 1
            program = ""
            child_indices = []
            for _ in range(num_vars):
                child_indices.append(index)
                index, add_program = encode_formula_tree(
                    index,
                    formula.child,
                    num_vars,
                    polarity,
                )
                program = add_program + program
            if isinstance(formula, Diamond):
                program += f"ft_node({orig_index},diamond,{posneg}).\n"
            elif isinstance(formula, Box):
                program += f"ft_node({orig_index},box,{posneg}).\n"
            edge_type = "choice_rel"
            if ((isinstance(formula, Diamond) and not polarity) or \
                (isinstance(formula, Box) and polarity)):
                edge_type = "full_rel"
            for child_index in child_indices:
                program += f"ft_edge({orig_index},{child_index},{edge_type}).\n"
            return index, program

    _, program = encode_formula_tree(
        1,
        formula,
        num_vars,
        polarity,
    )
    return program + "ft_root(1).\n"


def solve_bsml_sat(
    sat_formula,
    unsat_formula,
    max_num_worlds=4,
    num_vars=3,
    verbose=True,
    custom_program=None,
    timeout=None,
    use_minimization_heuristics=False,
    symmetry_breaking_variant=2,
):

    sat_formula_program = encode_formula_tree(
        formula_to_nf(sat_formula),
        num_vars,
        True,
    )

    unsat_formula_program = encode_formula_tree(
        formula_to_nf(unsat_formula),
        num_vars,
        True,
    )

    # Guess a Kripke model
    model_program = f"""
        #const n = {max_num_worlds}.
        #const v = {num_vars}.
        var(1..v).
        world(1..n).
    """
    model_program += """
        % Guess a valuation
        { valuation(W,V) : world(W), var(V) }.

        % Guess a relation
        { relation(W1,W2) : world(W1), world(W2) }.

        #show world/1.
        #show valuation/2.
        #show relation/2.
    """
    # Symmetry breaking
    if symmetry_breaking_variant == 1:
        # Simple symmetry breaking
        model_program += """
            % Symmetry breaking: order worlds by their out-degree
            out_degree(W1,D) :- world(W1), D = #count { W2 : relation(W1,W2) }.
            :- out_degree(W1,D1), out_degree(W2,D2), W2 > W1, D2 < D1.
            %in_degree(W1,D) :- world(W1), D = #count { W2 : relation(W2,W1) }.
            %:- out_degree(W1,D), out_degree(W2,D), W2 > W1,
            %    in_degree(W1,D1), in_degree(W2,D2), D2 < D1.
        """
    elif symmetry_breaking_variant == 2:
        # Symmetry breaking for directed graphs
        # from the paper "Symmetry-Breaking Constraints for Directed Graphs"
        # by Jussi Rintanen and Masood Feyzbakhsh Rankooh
        # (doi.org/10.3233/FAIA240998)
        model_program += """
            sb_max_index(n).
            sb_index(1..M) :- sb_max_index(M).
            sb_pair(I,J) :- sb_index(I), sb_index(J), I < J.

            sb_seq_length(I,J,2*N-1) :- sb_pair(I,J), sb_max_index(N).
            sb_triple(I,J,1..L) :- sb_pair(I,J), sb_seq_length(I,J,L).

            sb_statement(I,J,K,first,relation(K,I)) :-
                sb_triple(I,J,K),
                K < I.
            sb_statement(I,J,K,first,relation(I,K-I+1)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I, K < I+N.
            sb_statement(I,J,K,first,relation(K-N+1,I)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I+N.

            sb_statement(I,J,K,second,relation(K,J)) :-
                sb_triple(I,J,K),
                K < I.
            sb_statement(I,J,K,second,relation(J,K-I+1)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I, K < I+N,
                K-I+1 != I, K-I+1 != J.
            sb_statement(I,J,K,second,relation(J,J)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I, K < I+N,
                K-I+1 = I.
            sb_statement(I,J,K,second,relation(J,I)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I, K < I+N,
                K-I+1 = J.
            sb_statement(I,J,K,second,relation(K-N+1,J)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I+N,
                K-N+1 != J.
            sb_statement(I,J,K,second,relation(I,J)) :-
                sb_triple(I,J,K), sb_max_index(N),
                K >= I+N,
                K-N+1 = J.

            sb_y(I,J,0) :- sb_pair(I,J).
            :- sb_triple(I,J,K),
                sb_statement(I,J,K,first,relation(F1,F2)),
                sb_statement(I,J,K,second,relation(S1,S2)),
                sb_y(I,J,K-1), relation(F1,F2), not relation(S1,S2).
            sb_y(I,J,K) :- sb_triple(I,J,K), K < L, sb_seq_length(I,J,L),
                sb_statement(I,J,K,first,relation(F1,F2)),
                sb_y(I,J,K-1), relation(F1,F2).
            sb_y(I,J,K) :- sb_triple(I,J,K), K < L, sb_seq_length(I,J,L),
                sb_statement(I,J,K,second,relation(S1,S2)),
                sb_y(I,J,K-1), not relation(S1,S2).
        """

    # Express the semantics
    semantics_program = """
        % Guess states for each (active) node
        { state(N,W) : world(W) } :- ft_node(N,_,_), ft_active(N).
        #show state(W) : state(R,W), ft_root(R).

        % Auxiliary predicates
        state_nonempty(N) :- ft_node(N,_,_), state(N,W).
        state_empty(N) :- ft_node(N,_,_), not state(N,W) : world(W).

        % Redundant: inactive nodes have empty states
        :- ft_node(N,_,_), not ft_active(N),
            state(N,W), world(W).

        % Guess which nodes are active
        { ft_active(N) : ft_node(N,_,_) }.
        % Root must be active
        :- not ft_active(R), ft_root(R).
        % Inactivity propagates down in the tree
        :- ft_node(N1,_,_), ft_edge(N1,N2,_),
            not ft_active(N1), ft_active(N2).
        % Inactivity propagates to the right for siblings in the tree
        % (or equally: activity propagates to the left for siblings)
        ft_right_sibling(N1,N2) :- ft_edge(N,N1,_), ft_edge(N,N2,_),
            N1 < N2.
        :- ft_right_sibling(N1,N2), not ft_active(N1), ft_active(N2).
        % Activity propagates down for equal and join nodes
        :- ft_edge(N1,N2,equal), ft_active(N1), not ft_active(N2).
        :- ft_edge(N1,N2,join), ft_active(N1), not ft_active(N2).

        % Active nodes linked with 'equal' edge must have the same state
        :- ft_node(N1,_,_), ft_node(N2,_,_),
            ft_active(N1), ft_active(N2), ft_edge(N1,N2,equal),
            state(N1,W), not state(N2,W).
        :- ft_node(N1,_,_), ft_node(N2,_,_),
            ft_active(N1), ft_active(N2), ft_edge(N1,N2,equal),
            not state(N1,W), state(N2,W).

        % 'Join' node's children's states represent a union of the parent state
        :- ft_node(N1,_,_), ft_edge(N1,_,join), ft_active(N1),
            state(N1,W), not state(N2,W) : ft_edge(N1,N2,join).
        :- ft_node(N1,_,_), ft_edge(N1,N2,join), ft_active(N1),
            state(N2,W), not state(N1,W).

        % Active 'choice_rel' node with empty state has only inactive children
        :- ft_node(N1,_,_), ft_edge(N1,N2,choice_rel), ft_active(N1),
            state_empty(N1), ft_active(N2).

        % Active 'choice_rel' node's children provide successor states
        1 { state_successor(N2,W) : ft_edge(N1,N2,choice_rel) } :-
            ft_node(N1,_,_), ft_edge(N1,_,choice_rel),
            state(N1,W), ft_active(N1).
        :- state_successor(N,W1), state(N,W2), not relation(W1,W2).
        :- state_successor(N,_), not ft_active(N).

        % Active 'choice_rel' successors may not be empty
        :- ft_edge(_,N2,choice_rel), ft_active(N2), state_empty(N2).

        % Active 'full_rel' node with empty state has only inactive children
        :- ft_node(N1,_,_), ft_edge(N1,N2,full_rel), ft_active(N1),
            state_empty(N1), ft_active(N2).

        % Active 'full_rel' node's children provide 'full' successor states
        1 { state_full_successor(N2,W) : ft_edge(N1,N2,full_rel) } :-
            ft_node(N1,_,_), ft_edge(N1,_,full_rel),
            state(N1,W), ft_active(N1).
        :- state_full_successor(N,W1), state(N,W2), not relation(W1,W2).
        :- state_full_successor(N,W1), not state(N,W2), relation(W1,W2).
        :- state_full_successor(N,_), not ft_active(N).

        % Truth conditions for variables
        :- ft_node(N,var(V),pos), ft_active(N),
            not valuation(W,V), state(N,W).
        :- ft_node(N,var(V),neg), ft_active(N),
            valuation(W,V), state(N,W).

        % Truth conditions for bottom
        :- ft_node(N,bottom,pos), ft_active(N),
            state_empty(N).

        % Truth conditions for NE
        :- ft_node(N,ne,pos), ft_active(N),
            state_empty(N).
        :- ft_node(N,ne,neg), ft_active(N),
            state_nonempty(N).

        % (Truth conditions for diamond/box/conjunction/disjunction/negation
        % are implemented implicitly)

        % Symmetry breaking: lexicographic ordering of states for choice_rel
        % and full_rel children
        %%% TODO (and also check if it's actually helpful)
    """

    program = "#program guess.\n"
    program += model_program
    if custom_program:
        program += custom_program

    program += sat_formula_program
    program += semantics_program

    # Add minimization heuristics, if needed
    heuristics_program = """
        #heuristic relation(W1,W2) : world(W1), world(W2). [10,false]
        #heuristic state(1,1). [10,true]
        #heuristic valuation(W,V) : world(W), var(V). [10,false]
        #heuristic world(W) : possible_world(W), W > 1. [10,false]
    """
    if use_minimization_heuristics:
        program += heuristics_program

    program += "#program check.\n"
    program += unsat_formula_program
    program += semantics_program
    program += f"""
        world(1..{max_num_worlds}).
        var(1..{num_vars}).
    """
    # program += """
    #     relevant(valuation(W,V)) :- world(W), var(V).
    #     relevant(relation(W1,W2)) :- world(W1), world(W2).
    #     relevant(state(1,W)) :- world(W).
    # """
    program += """
        relevant(state(1,W)) :- world(W).

        relevant(relation(W1,W2)) :- state_successor(N,W1), state(N,W2).
        relevant(relation(W1,W2)) :- state_full_successor(N,W1), world(W2).

        relevant(valuation(W,V)) :- ft_node(N,var(V),_), ft_active(N),
            state(N,W).
    """

    program += "#program glue.\n"
    program += f"""
        world(1..{max_num_worlds}).
        var(1..{num_vars}).
    """
    program += """
        valuation(W,V) :- world(W), var(V).
        relation(W1,W2) :- world(W1), world(W2).
        state(1,W) :- world(W).

        #show world/1.
        #show valuation/2.
        #show relation/2.
        #show state/2.
    """

    def on_model(model):
        solution = [
            str(atom) for atom in model.symbols(shown=True)
        ]
        solution.sort()
        print("## Solution ##")
        for atom in solution:
            print(atom)

    solve_gcc(program, on_model, timeout)
