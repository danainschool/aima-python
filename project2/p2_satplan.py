from planning import air_cargo, Action
from utils import expr
from logic import FolKB, PropKB, SAT_plan
from search import Problem, Graph


class PlanningProblem(Problem):
    def __init__(self, pddl):
        self.pddl = pddl
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


if __name__ == '__main__':
    # p = air_cargo()
    # print(p.goal_test())
    # print(p.kb.clauses)
    # for action in p.actions:
    #     print(action.name)
    cargos = ['C1', 'C2']
    planes = ['P1', 'P2']
    airports = ['JFK', 'SFO']

    pddl = air_cargo()
    p = AirCargoPlanningProblem(pddl, cargos, planes, airports)
    print("\n*** Transitions ***")
    for a in p.prop_actions:
        precond = a.precond_pos
        for clause in a.precond_neg:
            if clause in precond:
                precond.remove(clause)
        for clause in p.atemporal_literals():
            if clause in precond:
                precond.remove(clause)

        effect = precond
        for clause in a.effect_add:
            if clause not in effect:
                effect.extend(a.effect_add)
        for clause in a.effect_rem:
            if clause in effect:
                effect.remove(clause)
        for clause in p.atemporal_literals():
            if clause in effect:
                effect.remove(clause)

        print("{} -> {}{} -> {}".format(precond,a.name, a.args, effect))
    print("\n*** Initial ***")
    print(p.initial)
    print("\n*** Goal ***")
    print(p.goal)
    print("\n*** Fluents ***")
    print(p.fluents)




