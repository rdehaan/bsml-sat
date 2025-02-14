"""
Example guess and check based solver for second level problems.
"""

import sys
from typing import Sequence, Tuple, List, cast

from clingo import ast
from clingo.solving import SolveResult
from clingo.ast import ProgramBuilder
from clingo.control import Control
from clingo.application import clingo_main, Application
from clingo.propagator import PropagateControl, PropagateInit, Propagator
from clingo.backend import Backend
from clingo.ast import parse_string, AST, ASTType


class Transformer:
    """
    Transformer for the guess and check solver.
    """
    _builder: ProgramBuilder
    _state: str
    _check: List[AST]
    _glue: List[AST]

    def __init__(
        self,
        builder: ProgramBuilder,
        check: List[AST],
        glue: List[str]
    ):
        self._builder = builder
        self._state = "guess"
        self._check = check
        self._glue = glue

    def add(self, stm: AST):
        """
        Add the given statement to the guess or check programs.
        """
        if stm.ast_type == ASTType.Program:
            if stm.name == "glue" and not stm.parameters:
                self._state = "glue"
            elif stm.name == "check" and not stm.parameters:
                self._state = "check"
            elif (stm.name in ["base", "guess"]) and not stm.parameters:
                self._state = "guess"
            else:
                raise RuntimeError("unexpected program part")

        else:
            if self._state == "guess":
                self._builder.add(stm)
            elif self._state == "check":
                self._check.append(stm)
            elif self._state == "glue":
                self._glue.append(stm)


class Checker:
    """
    Class wrapping a solver to perform the second level check.
    """
    _ctl: Control
    _map: List[Tuple[int, int]]

    def __init__(self):
        self._ctl = Control()
        self._map = []

    def backend(self) -> Backend:
        """
        Return the backend of the underlying solver.
        """
        return self._ctl.backend()

    def add(self, guess_lit: int, check_lit: int):
        """
        Map the given solver literal to the corresponding program literal in
        the checker.
        """
        self._map.append((guess_lit, check_lit))

    def ground(self, check: Sequence[ast.AST]):
        """
        Ground the check program.
        """
        with ProgramBuilder(self._ctl) as bld:
            for stm in check:
                bld.add(stm)

        self._ctl.ground([("base", [])])

    def check(self, control: PropagateControl) -> bool:
        """
        Return true if the check program is unsatisfiable w.r.t. to the atoms
        of the guess program.

        The truth values of the atoms of the guess program are stored in the
        assignment of the given control object.
        """

        assignment = control.assignment

        assumptions = []
        for guess_lit, check_lit in self._map:
            guess_truth = assignment.value(guess_lit)
            assumptions.append(check_lit if guess_truth else -check_lit)

        ret = cast(SolveResult, self._ctl.solve(assumptions))
        if ret.unsatisfiable is not None:
            return ret.unsatisfiable

        raise RuntimeError("search interrupted")


class CheckPropagator(Propagator):
    """
    Simple propagator verifying that a check program holds on total
    assignments.
    """
    _check: List[AST]
    _glue: List[str]
    _checkers: List[Checker]
    _gluelits: List[int]

    def __init__(self, check: List[AST], glue: List[AST]):
        self._check = check
        self._glue = glue
        self._checkers = []
        self._gluelits = []

    def init(self, init: PropagateInit):
        """
        Initialize the solvers for the check programs.
        """
        # we need a checker for each thread (to be able to solve in parallel)
        for _ in range(init.number_of_threads):
            checker = Checker()
            self._checkers.append(checker)

            with checker.backend() as backend:
                for atom in init.symbolic_atoms:

                    # ignore atoms that are not glue
                    if str(atom.symbol) not in self._glue:
                        # print(f"Skipping atom {atom.symbol}")
                        continue

                    guess_lit = init.solver_literal(atom.literal)
                    guess_truth = init.assignment.value(guess_lit)

                    # ignore false atoms
                    if guess_truth is False:
                        continue

                    check_lit = backend.add_atom(atom.symbol)

                    # print(f"Adding atom {atom.symbol} as guess_lit {guess_lit} and check_lit {check_lit}..")

                    if guess_lit not in self._gluelits:
                        self._gluelits.append(guess_lit)

                    # fix true atoms
                    if guess_truth is True:
                        backend.add_rule([check_lit], [])

                    # add a choice rule for unknow atoms and add them to the
                    # mapping table of the checker
                    else:
                        backend.add_rule([check_lit], [], True)
                        checker.add(guess_lit, check_lit)

            checker.ground(self._check)


    def check(self, control: PropagateControl):
        """
        Check total assignments.
        """
        assignment = control.assignment
        checker = self._checkers[control.thread_id]

        if not checker.check(control):

            conflict = []

            # for level in range(1, assignment.decision_level+1):
            #     conflict.append(-assignment.decision(level))

            # for lit in self._gluelits:
            #     if assignment.has_literal(lit):
            #         if assignment.is_true(lit):
            #             conflict.append(-lit)
            #         elif assignment.is_false(lit):
            #             conflict.append(lit)

            for lit in self._gluelits:
                conflict.append(-lit if assignment.is_true(lit) else lit)

            # print(f"Adding clause: {conflict}")

            control.add_clause(conflict)


def solve_gcc(program, on_model, timeout=None, verbose=True):

    ctl = Control([
        "--project",
        "-Wnone",
        "--heuristic=Domain",
        # "--parallel-mode=4", # See: https://github.com/potassco/clingo/issues/166
    ])

    check: List[AST] = []
    glue: List[AST] = []
    with ProgramBuilder(ctl) as bld:
        trans = Transformer(bld, check, glue)
        parse_string(program, trans.add)

    # Take glue program, find a model, and collects its shown atoms as str
    glue_ctl = Control()
    with ProgramBuilder(glue_ctl) as glue_bld:
        for stm in glue:
            glue_bld.add(stm)
    glue_ctl.ground([("base", [])])
    glue_ctl.configuration.solve.models = 1
    glue = []
    def on_glue_model(model):
        for atom in model.symbols(shown=True):
            glue.append(str(atom))
    glue_ctl.solve(on_model=on_glue_model)

    ctl.register_propagator(CheckPropagator(check, glue))

    if verbose:
        print(".. Grounding ..")
    ctl.ground([("base", [])])
    ctl.configuration.solve.models = 1
    if verbose:
        print(".. Solving ..\n")

    # with ctl.solve(yield_=True) as handle:
    #     for model in handle:
    #         on_model(model)
    #     handle.get()
    with ctl.solve(on_model=on_model, async_=True) as handle:
        if timeout:
            finished = handle.wait(timeout)
            if finished:
                print("Finished the search within time limit..")
            else:
                print("Did not finish the search within time limit..")
        else:
            handle.wait()

    if verbose:
        print("\n.. Done solving ..")
        print(f"Total solving time: {ctl.statistics['summary']['times']['solve']:.2f} sec")
