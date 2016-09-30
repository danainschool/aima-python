from planning import *
from utils import expr
from logic import FolKB

cargos = ['C1', 'C2']
planes = ['P1', 'P2']
airports = ['JFK', 'SFO']

def load_literals(cargos, planes, airports):
    count = 0
    loads = []
    for c in cargos:
        for p in planes:
            for a in airports:
                precond_pos = [expr("At({}, {})".format(c,a)),
                               expr("At({}, {})".format(p,a)),
                               expr("Cargo({})".format(c)),
                               expr("Plane({})".format(p)),
                               expr("Airport({})".format(a)),
                               ]
                precond_neg = []
                effect_add = [expr("In({}, {})".format(c,p))]
                effect_rem = [expr("At({}, {})".format(c,a))]
                load = Action(expr("Load{}({}, {}, {})".format(count, c, p, a)),
                              [precond_pos, precond_neg],
                              [effect_add, effect_rem])
                loads.append(load)
                count += 1
    return loads

def unload_literals(cargos, planes, airports):
    count = 0
    unloads = []
    for c in cargos:
        for p in planes:
            for a in airports:
                precond_pos = [expr("In({}, {})".format(c,p)),
                               expr("At({}, {})".format(p,a)),
                               expr("Cargo({})".format(c)),
                               expr("Plane({})".format(p)),
                               expr("Airport({})".format(a)),
                               ]
                precond_neg = []
                effect_add = [expr("At({}, {})".format(c,a))]
                effect_rem = [expr("In({}, {})".format(c,p))]
                load = Action(expr("Unload{}({}, {}, {})".format(count, c, p, a)),
                              [precond_pos, precond_neg],
                              [effect_add, effect_rem])
                unloads.append(load)
                count += 1
    return unloads

def fly_literals(planes, airports):
    count = 0
    flys = []
    for f in airports:
        for p in planes:
            for to in airports:
                precond_pos = [expr("At({}, {})".format(p,f)),
                               expr("Airport({})".format(f)),
                               expr("Plane({})".format(p)),
                               expr("Airport({})".format(to)),
                               ]
                precond_neg = []
                effect_add = [expr("At({}, {})".format(p,to))]
                effect_rem = [expr("At({}, {})".format(p,f))]
                load = Action(expr("Fly{}({}, {}, {})".format(count, p, f, to)),
                              [precond_pos, precond_neg],
                              [effect_add, effect_rem])
                flys.append(load)
                count += 1
    return flys

def ac_initial():
    init = [expr('At(C1, SFO)'),
            expr('At(C2, JFK)'),
            expr('At(P1, SFO)'),
            expr('At(P2, JFK)'),
            expr('Cargo(C1)'),
            expr('Cargo(C2)'),
            expr('Plane(P1)'),
            expr('Plane(P2)'),
            expr('Airport(JFK)'),
            expr('Airport(SFO)')]
    neg = [expr('~At(C2, SFO)'),
           ]


if __name__ == '__main__':
    # p = air_cargo()
    # print(p.goal_test())
    # print(p.kb.clauses)
    # for action in p.actions:
    #     print(action.name)
    '''
    Section 10.4.3 Classical planning as Boolean satisfiability
    Convert PDDL to PL
    Step 1 Propositionalize the actions
    '''
    action_literals=load_literals(cargos, planes, airports)\
                + unload_literals(cargos,planes, airports)\
                + fly_literals(planes, airports)
    for a in action_literals:
        print(a.name)
    '''
    Step 2 Define the initial state positive negative
    '''

