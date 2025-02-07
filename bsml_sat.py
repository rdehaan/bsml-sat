import clingo

from abc import ABC, abstractmethod

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


def formula_to_asp_facts(formula):

    def fact_constructor(index, formula):
        if isinstance(formula, Var):
            return index+1, f"subformula({index},var({formula.name})).\n"
        if isinstance(formula, NE):
            return index+1, f"subformula({index},ne).\n"
        if isinstance(formula, Bottom):
            return index+1, f"subformula({index},bottom).\n"
        if isinstance(formula, (And, Or)):
            orig_index = index
            index += 1
            program = ""
            child_indices = []
            for child in formula.children:
                child_indices.append(index)
                index, add_program = fact_constructor(index, child)
                program += add_program
            if isinstance(formula, Or):
                program += f"subformula({orig_index},or).\n"
            if isinstance(formula, And):
                program += f"subformula({orig_index},and).\n"
            for child_index in child_indices:
                program += f"child({orig_index},{child_index}).\n"
            return index, program
        if isinstance(formula, (Diamond, Box, Neg)):
            if isinstance(formula, Diamond):
                program = f"subformula({index},diamond).\n"
            elif isinstance(formula, Box):
                program = f"subformula({index},box).\n"
            elif isinstance(formula, Neg):
                program = f"subformula({index},neg).\n"
            program += f"child({index},{index+1}).\n"
            index, add_program = fact_constructor(index+1, formula.child)
            program += add_program
            return index, program

    _, program = fact_constructor(1, formula)
    return program + "formula_root(1).\n"


def solve_bsml_sat(
    formula,
    max_num_worlds=4,
    num_vars=3,
    max_size_state_tree=8,
    verbose=True,
    use_minimization_heuristics=False,
):

    formula_program = formula_to_asp_facts(formula_to_nf(formula))

    model_program = f"""
        possible_world(1..{max_num_worlds}).
        var(1..{num_vars}).
        state_node(1..{max_size_state_tree}).
    """
    model_program += """
        { world(W) : possible_world(W) }.
        world(W-1) :- world(W), possible_world(W-1).
        :- not world(1).

        { valuation(W,V) : world(W), var(V) }.

        { relation(W1,W2) : world(W1), world(W2) }.

        state_root(1).

        { state(N,W) : world(W) } :- state_node(N).

        state_nonempty(N) :- state_node(N), state(N,W).
        state_empty(N) :- state_node(N), not state(N,W) : world(W).

        state_type(join;relation;full_relation;leaf;inactive).
        1 { state_type(N,T) : state_type(T) } 1 :- state_node(N).

        :- state_type(R,inactive), state_root(R).
        :- state_type(N,inactive), state_nonempty(N).

        1 { state_edge(N,M) : state_node(M), N != M } :-
            state_type(N,join), state_nonempty(N).
        :- state_type(N,join),
            state(N,W), not state(M,W) : state_edge(N,M).
        :- state_type(N,join),
            state_edge(N,M), state(M,W), not state(N,W).

        1 { state_edge(N,M) : state_node(M), N != M } :-
            state_type(N,relation), state_nonempty(N).
        :- state_type(N,relation), state_edge(N,M), state_empty(M).
        1 { state_successor(M,W) : state_edge(N,M) } 1 :-
            state_type(N,relation), state(N,W).
        :- state_successor(M,W1), state(M,W2), not relation(W1,W2).

        1 { state_edge(N,M) : state_node(M), N != M } :-
            state_type(N,full_relation), state_nonempty(N).
        1 { state_full_successor(M,W) : state_edge(N,M) } 1 :-
            state_type(N,full_relation), state(N,W).
        :- state_full_successor(M,W1), state(M,W2), not relation(W1,W2).
        :- state_full_successor(M,W1), relation(W1,W2), not state(M,W2).

        :- state_node(N),
            not state_root(N),
            not state_edge(M,N) : state_node(M);
            not state_type(N,inactive).

        state_edge_trans(N1,N2) :- state_edge(N1,N2).
        state_edge_trans(N1,N3) :- state_edge_trans(N1,N2), state_edge(N2,N3).
        :- state_edge_trans(N,N).
        :- state_edge(N1,N3), state_edge(N2,N3), N1 != N2.
        :- state_edge(N,M), M <= N.

        states_identical(N1,N2) :- state_node(N1), state_node(N2), N1 != N2,
            state(N1,W) : state(N2,W);
            state(N2,W) : state(N1,W).

        :- state_edge(N1,N2), state_edge(N1,N3),
            states_identical(N2,N3),
            state_type(N2,T), state_type(N3,T).

        %%% SYMMETRY BREAKING:

        :- state_edge(N1,N2), state_type(N1,inactive).
        :- state_edge(N1,N2), state_type(N2,inactive).
        :- state_node(N1), state_node(N2), N2 > N1,
            state_type(N1,inactive), not state_type(N2,inactive).

        out_degree(W1,D) :- world(W1), D = #count { W2 : relation(W1,W2) }.
        :- out_degree(W1,D1), out_degree(W2,D2), W2 > W1, D2 < D1.
        %in_degree(W1,D) :- world(W1), D = #count { W2 : relation(W2,W1) }.
        %:- out_degree(W1,D), out_degree(W2,D), W2 > W1,
        %    in_degree(W1,D1), in_degree(W2,D2), D2 < D1.

        siblings(N1,N2) :- state_node(N1), state_node(N2), N1 != N2,
            state_edge(N,N1), state_edge(N,N2).
        has_sibling(N1) :- siblings(N1,N2).
        direct_family(N1,N2) :- siblings(N1,N2).
        direct_family(N1,N2) :- state_edge(N1,N2).
        direct_family(N1,N2) :- state_edge(N2,N1).
        :- state_node(N), state_node(N+1), state_node(N+2),
            not state_type(N,inactive),
            not state_type(N+1,inactive),
            not state_type(N+2,inactive),
            has_sibling(N+1),
            not direct_family(N,N+1),
            not direct_family(N+1,N+2).

        #show world/1.
        #show valuation/2.
        #show relation/2.
        #show state(W) : state(R,W), state_root(R).
    """

    semantics_program = """
        %%% AUXILIARY
        support(F,N1) :- state_edge(N1,N2), states_identical(N1,N2), support(F,N2).
        antisupport(F,N1) :- state_edge(N1,N2), states_identical(N1,N2), antisupport(F,N2).

        %%% VAR
        support(F,N) :- subformula(F,var(V)), state_node(N),
            valuation(W,V) : state(N,W).
        antisupport(F,N) :- subformula(F,var(V)), state_node(N),
            not valuation(W,V) : state(N,W).

        %%% NEG
        support(F1,N) :- subformula(F1,neg), state_node(N),
            child(F1,F2), antisupport(F2,N).
        antisupport(F1,N) :- subformula(F1,neg), state_node(N),
            child(F1,F2), support(F2,N).

        %%% OR
        child_supported(F1,F2,N1) :- subformula(F1,or), state_node(N1),
            state_type(N1,join), child(F1,F2), state_edge(N1,N2),
            support(F2,N2).
        state_child_supported(F1,N1,N2) :- subformula(F1,or), state_node(N1),
            state_type(N1,join), child(F1,F2), state_edge(N1,N2),
            support(F2,N2).
        support(F1,N1) :- subformula(F1,or), state_node(N1),
            state_type(N1,join),
            child_supported(F1,F2,N1) : child(F1,F2);
            state_child_supported(F1,N1,N2) : state_edge(N1,N2).
        antisupport(F1,N) :- subformula(F1,or), state_node(N),
            antisupport(F2,N) : child(F1,F2).

        %%% AND
        child_antisupported(F1,F2,N1) :- subformula(F1,and), state_node(N1),
            state_type(N1,join), child(F1,F2), state_edge(N1,N2),
            antisupport(F2,N2).
        state_child_antisupported(F1,N1,N2) :- subformula(F1,and), state_node(N1),
            state_type(N1,join), child(F1,F2), state_edge(N1,N2),
            antisupport(F2,N2).
        support(F1,N) :- subformula(F1,and), state_node(N),
            support(F2,N) : child(F1,F2).
        antisupport(F1,N1) :- subformula(F1,and), state_node(N1),
            state_type(N1,join),
            child_antisupported(F1,F2,N) : child(F1,F2);
            state_child_antisupported(F1,N1,N2) : state_edge(N1,N2).

        %%% BOT
        support(F,N) :- subformula(F,bottom), state_node(N),
            not state(N,W) : world(W).
        antisupport(F,N) :- subformula(F,bottom), state_node(N).

        %%% NE
        support(F,N) :- subformula(F,ne), state_node(N),
            state(N,W).
        antisupport(F,N) :- subformula(F,ne), state_node(N),
            not state(N,W) : world(W).

        %%% DIAMOND
        support(F1,N1) :- subformula(F1,diamond), state_node(N1),
            state_type(N1,relation), child(F1,F2),
            support(F2,N2) : state_edge(N1,N2).
        antisupport(F1,N1) :- subformula(F1,diamond), state_node(N1),
            state_type(N1,full_relation), child(F1,F2),
            antisupport(F2,N2) : state_edge(N1,N2).
    """

    query_program = """
        %%% MAKE ROOT FORMULA TRUE IN ROOT OF STATE TREE
        :- not support(F,R), state_root(R), formula_root(F).
    """

    heuristics_program = """
        #heuristic relation(W1,W2) : world(W1), world(W2). [10,false]
        #heuristic state(1,1). [10,true]
        #heuristic valuation(W,V) : world(W), var(V). [10,false]
        #heuristic world(W) : possible_world(W), W > 1. [10,false]
    """

    program = formula_program
    program += model_program
    program += semantics_program
    program += query_program
    if use_minimization_heuristics:
        program += heuristics_program

    control = clingo.Control(
        ["--project", "-Wnone", "--heuristic=Domain", "--parallel-mode=4"]
    )
    control.add("base", [], program)
    if verbose:
        print(".. Grounding ..")
    control.ground([("base", [])])
    control.configuration.solve.models = 1
    if verbose:
        print(".. Solving ..\n")
    graphs = []
    found_solution = False
    with control.solve(yield_=True) as handle:
        for model in handle:
            found_solution = True
            solution = [
                str(atom) for atom in model.symbols(shown=True)
            ]
            solution.sort()
            if verbose:
                print("## Model witnessing satisfiability ##")
                for atom in solution:
                    print(atom)
                print()
        handle.get()

    if found_solution:
        print("BSML formula satisfiable!")
    else:
        print("BSML formula unsatisfiable!")

    if verbose:
        print("\n.. Done solving ..")
        print(f"Total solving time: {control.statistics['summary']['times']['solve']:.2f} sec")
