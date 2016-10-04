from planning import air_cargo, Action
from utils import expr, Expr
from logic import PropKB, dpll_satisfiable, associate
from search import Problem, Graph
import itertools


class SuccessorAxiom():
    def __init__(self, fluent_string, act_cause_list, act_cause_not_list):
        # where the cause lists are disjunction lists of conjunction lists
        self.transition = {fluent_string: {'act_causes': act_cause_list, 'act_causes_not': act_cause_not_list}}

class PreconditionAxiom():
    def __init__(self, action_string, precondition_list):
        self.precondition = {action_string: precondition_list}

def SAT_plan2(init, transition, precondition, goal, t_max, SAT_solver=dpll_satisfiable):
    """Converts a planning problem to Satisfaction problem by translating it to a cnf sentence.

    [Figure 7.22]
    Dana Sheahen: revised to match book:
         transition is now a list of successor state axioms (not sas') in form
         defined by the SuccessorAxiom class:
         [{Fstring1:{"act_causes":[], "act_cause_not":[]},
          {Fstring2:{"act_causes":[], "act_cause_not":[]},
          ...]
         working with fluents, not states
    """

    def expand_or_actions(act_list, t):
        act_clauses = []
        for a in act_list:
            act_clauses.append(action_sym[a, t])
        return associate('|', act_clauses)

    def expand_and_fluents(fluent_list, t):
        fluent_clauses = []
        for f in fluent_list:
            fluent_clauses.append((fluent_sym[f, t]))
        return associate('&', fluent_clauses)

    def translate_to_SAT(init, transition, goal, time):

        clauses = []
        fluents = [fluent for fluent in transition]

        # Symbol claiming fluent f at time t
        fluent_counter = itertools.count()
        for f in fluents:
            for t in range(time + 1):
                fluent_sym[f, t] = Expr("Fluent_{}".format(next(fluent_counter)))

        # collect all the unique actions from the transition axioms
        action_set = set()
        for f in fluents:
            for key in f:
                for action in f[key]:
                    action_set.add(action)

        # Symbol claiming action at time t
        action_counter = itertools.count()
        for action in action_set:
            for time in range(time + 1):
                action_sym[action, t] = Expr("Action_{}".format(next(action_counter)))

        # Add initial state axiom
        for clause in init:
            clauses.append(fluent_sym[clause, 0])

        # Add goal state axiom
        for clause in goal:
            clauses.append(fluent_sym[clause, time])

        # add successor state axioms defined 7.7.1 and 10.4.1 (sentence for each fluent)
        for f in transition:
            action_causes = transition[f]
            for t in range(time):
                clauses.append(expr("{} <==> ({}) | ({} & ~({})".format(
                    fluent_sym[f, t + 1],
                    expand_or_actions(action_causes['act_causes'], t),
                    fluent_sym[f, t],
                    expand_or_actions(action_causes['act_causes_not'], t)
                )))

        # TODO add precondition axioms defined 7.7.4 and 10.4.1
        # A_t ==> PRE(A)_t
        for a in precondition:
            fluents_pre = precondition[a]
            for t in range(time):
                clauses.append(expr("{} ==> {}".format(
                    action_sym[a, t],
                    expand_and_fluents(fluents_pre,t),
                )))


        # # TODO - is this needed?  not using "states" and doesn't apply to fluents
        # Allow only one state at any time
        # for t in range(time + 1):
        #     # must be a state at any time
        #     clauses.append(associate('|', [fluent_sym[s, t] for f in fluents]))
        #
        #     for f in fluents:
        #         for s_ in fluents[fluents.index(f) + 1:]:
        #             # for each pair of states s, s_ only one is possible at time t
        #             clauses.append((~fluent_sym[f, t]) | (~fluent_sym[s_, t]))

        # add action exclusion axioms defined 7.7.4
        # ~A(i)_t | ~A(j)_t
        for t in range(time):
            # list of possible actions at time t
            action_t = [a for a in action_sym if a[1] == t]

            # make sure at least one of the transitions happens
            # TODO find reference - is this already taken care of?
            clauses.append(associate('|', [action_sym[a] for a in action_t]))

            for a in action_t:
                for a_ in action_t[action_t.index(a) + 1:]:
                    # there cannot be two actions a and a_ at time t
                     clauses.append(expr("~{} | ~{}".format(
                         action_sym[a], action_sym[a_],
                     )))

        # Combine the clauses to form the cnf
        return associate('&', clauses)

    def extract_solution(model):
        true_transitions = [t for t in action_sym if model[action_sym[t]]]
        # Sort transitions based on time, which is the 3rd element of the tuple
        true_transitions.sort(key=lambda x: x[2])
        return [action for s, action, time in true_transitions]

    # Body of SAT_plan algorithm
    for t in range(t_max):
        # dictionaries to help extract the solution from model
        fluent_sym = {}
        action_sym = {}

        cnf = translate_to_SAT(init, transition, goal, t)
        model = SAT_solver(cnf)
        if model is not False:
            return extract_solution(model)
    return None


class PlanningProblem(Problem):
    def __init__(self, pddl):
        self.pddl = pddl
        self.kb = PropKB()
        self.prop_actions = self.step1()
        Problem.__init__(self, initial=self.step2(), goal=self.step3())
        self.fluents = self.step4()
        self.graph = Graph()

    def actions(self, A):
        "The actions at a graph node are just its neighbors."
        return list(self.graph.get(A).keys())

    def result(self, state, action):
        "The result of going to a neighbor is just that neighbor."
        return action

    def transitions(self):
        # return all (s,a,s')
        raise NotImplementedError

    def make_prop_graph(self):
        raise NotImplementedError

    def step1(self):
        '''
        Section 10.4.3 Classical planning as Boolean satisfiability
        Convert PDDL to PL
        Step 1 Propositionalize the actions
        '''
        raise NotImplementedError

    def step2(self):
        '''
        Step 2 Define the initial state positive negative
        '''
        raise NotImplementedError

    def step3(self):
        '''
        Step 3 Propositionalize goal
        '''
        raise NotImplementedError

    def step4(self):
        '''
        Step 4 Add successor-state axioms
        '''
        raise NotImplementedError

    def step5(self):
        '''
        '''
        raise NotImplementedError


class AirCargoPlanningProblem(PlanningProblem):
    def __init__(self, pddl, cargos, planes, airports):
        self.cargos = cargos
        self.planes = planes
        self.airports = airports
        PlanningProblem.__init__(self, pddl)

    def atemporal_literals(self):
        atemps = set()
        for c in self.cargos:
            atemps.add(expr("Cargo({})".format(c)))
        for p in self.planes:
            atemps.add(expr("Plane({})".format(p)))
        for a in self.airports:
            atemps.add(expr("Airport({})".format(a)))
        return atemps

    def load_literals(self):
        count = 0
        loads = []
        for c in self.cargos:
            for p in self.planes:
                for a in self.airports:
                    precond_pos = [expr("At({}, {})".format(c, a)),
                                   expr("At({}, {})".format(p, a)),
                                   expr("Cargo({})".format(c)),
                                   expr("Plane({})".format(p)),
                                   expr("Airport({})".format(a)),
                                   ]
                    precond_neg = []
                    effect_add = [expr("In({}, {})".format(c, p))]
                    effect_rem = [expr("At({}, {})".format(c, a))]
                    load = Action(expr("Load{}({}, {}, {})".format(count, c, p, a)),
                                  [precond_pos, precond_neg],
                                  [effect_add, effect_rem])
                    loads.append(load)
                    count += 1
        return loads

    def unload_literals(self):
        count = 0
        unloads = []
        for c in self.cargos:
            for p in self.planes:
                for a in self.airports:
                    precond_pos = [expr("In({}, {})".format(c, p)),
                                   expr("At({}, {})".format(p, a)),
                                   expr("Cargo({})".format(c)),
                                   expr("Plane({})".format(p)),
                                   expr("Airport({})".format(a)),
                                   ]
                    precond_neg = []
                    effect_add = [expr("At({}, {})".format(c, a))]
                    effect_rem = [expr("In({}, {})".format(c, p))]
                    unload = Action(expr("Unload{}({}, {}, {})".format(count, c, p, a)),
                                    [precond_pos, precond_neg],
                                    [effect_add, effect_rem])
                    unloads.append(unload)
                    count += 1
        return unloads

    def fly_literals(self):
        count = 0
        flys = []
        for f in self.airports:
            for p in self.planes:
                for to in self.airports:
                    precond_pos = [expr("At({}, {})".format(p, f)),
                                   expr("Airport({})".format(f)),
                                   expr("Plane({})".format(p)),
                                   expr("Airport({})".format(to)),
                                   ]
                    precond_neg = []
                    effect_add = [expr("At({}, {})".format(p, to))]
                    effect_rem = [expr("At({}, {})".format(p, f))]
                    fly = Action(expr("Fly{}({}, {}, {})".format(count, p, f, to)),
                                 [precond_pos, precond_neg],
                                 [effect_add, effect_rem])
                    flys.append(fly)
                    count += 1
        return flys

    def step1(self):
        list = self.load_literals() + self.unload_literals() + self.fly_literals()
        return list

    def step2(self):
        init = [expr('At(C1, SFO)'),
                expr('At(C2, JFK)'),
                expr('At(P1, SFO)'),
                expr('At(P2, JFK)'),
                # expr('Cargo(C1)'),
                # expr('Cargo(C2)'),
                # expr('Plane(P1)'),
                # expr('Plane(P2)'),
                # expr('Airport(JFK)'),
                # expr('Airport(SFO)'),
                ]
        neg = [expr('~At(C2, SFO)'),
               expr('~In(C2, P1)'),
               expr('~In(C2, P2)'),
               expr('~At(C1, JFK)'),
               expr('~In(C1, P1)'),
               expr('~In(C1, P2)'),
               ]
        return init + neg

    def step3(self):
        return [expr('At(C1 , JFK) & At(C2 ,SFO)')]

    def step4(self):
        # fluents are set of unique add and rem effects except for atemporal variables
        fluents = set()
        for a in self.prop_actions:
            for f in a.precond_pos:
                fluents.add(f)
            for f in a.precond_neg:
                fluents.add(f)
            fluents = fluents.difference(self.atemporal_literals())
        return fluents

def test_SAT_plan():
    #FIXME should be lists of lists
    transition = [
        SuccessorAxiom('At(A)',['Left', 'At(B)'],['Right']),
        SuccessorAxiom('At(B)',['Left', 'Right'])]

    #     {'A': {'Left': 'A', 'Right': 'B'},
    #               'B': {'Left': 'A', 'Right': 'C'},
    #               'C': {'Left': 'B', 'Right': 'C'}}
    # assert SAT_plan('A', transition, 'C', 2) is None
    # assert SAT_plan('A', transition, 'B', 3) == ['Right']
    # assert SAT_plan('C', transition, 'A', 3) == ['Left', 'Left']

    transition = {(0, 0): {'Right': (0, 1), 'Down': (1, 0)},
                  (0, 1): {'Left': (1, 0), 'Down': (1, 1)},
                  (1, 0): {'Right': (1, 0), 'Up': (1, 0), 'Left': (1, 0), 'Down': (1, 0)},
                  (1, 1): {'Left': (1, 0), 'Up': (0, 1)}}
    assert SAT_plan2((0, 0), transition, (1, 1), 4) == ['Right', 'Down']

if __name__ == '__main__':
    # test this satplan
    pass

