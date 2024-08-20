r'''
SageMath code ver. 20240819 by Max Alekseyev
for computing terms of the following sequences:

* A373811 a(0) = 0. For n > 0, a(n) is the smallest number of straight lines needed to intersect all points (k, a(k)) for k < n.
* Run lengths: A373812

* A375499 a(n) is the smallest number of straight lines needed to intersect all points (k, d(k)) for k = 1..n (where d is the sum-of-divisors function A000005).
* Run lengths: A375515

* A373810 a(n) is the smallest number of straight lines needed to intersect all points (k, phi(k)) for k = 1..n (where phi is the Euler totient function A000010).
* Run lengths: A373815

* A373813 a(n) is the smallest number of straight lines needed to intersect all points (k, prime(k)) for k = 1..n.
* Run lengths: A373814

Approach is on representing lines as sets of points and solving the set cover problem with MILP.
'''

# Select a MILP solver:
mysolver = default_mip_solver()         # default choice
#mysolver = 'Gurobi'
#mysolver = 'Cplex'
#mysolver = 'ppl'
#mysolver = 'GLPK'

print('MILP solver:', mysolver)



######### Functions to compute individual terms

a375499 = lambda n: len( min_lines([(k, number_of_divisors(k)) for k in (1..n)]) )

a373810 = lambda n: len( min_lines([(k, euler_phi(k)) for k in (1..n)]) )

a373813 = lambda n: len( min_lines([(k, nth_prime(k)) for k in (1..n)]) )


######### Functions to extend sequences with many terms

def a373811_grow(a0=[0,1,1,2], by_jumps=True):
    if by_jumps:
        return func_grow_by_jumps(lambda a: tuple(enumerate(a)), a0, 'A373811')
    else:
        return func_grow_by_one(lambda a: tuple(enumerate(a)), a0, 'A373811')

def a375499_grow(a0=[0, 1, 1, 2, 2, 2, 3], by_jumps=True):
    func = func_grow_by_jumps if by_jumps else func_grow_by_one
    return func(lambda a: tuple((k,number_of_divisors(k)) for k in range(1,len(a)+1)), a0, 'A375499')

def a373810_grow(a0=[0, 1, 1, 2, 2, 2, 3], by_jumps=True):
    func = func_grow_by_jumps if by_jumps else func_grow_by_one
    return func(lambda a: tuple((k,euler_phi(k)) for k in range(1,len(a)+1)), a0, 'A373810')

def a373813_grow(a0=[0, 1, 1, 2, 2, 2, 3], by_jumps=True):
    func = func_grow_by_jumps if by_jumps else func_grow_by_one
    return func(lambda a: tuple((k,nth_prime(k)) for k in range(1,len(a)+1)), a0, 'A373813')


######### Low-level machinery

import time
from sage.numerical.mip import MIPSolverException

def on_same_line(p,q,r):
    '''
    Check if 2D points p,q,r are on the same line.
    '''
    return Matrix([[*p,1],[*q,1],[*r,1]]).det() == 0

@cached_function
def min_lines(points):
    '''
    Find a smallest set of lines covering the given points.
    '''

    if len(points) <= 1:
        return points

    lines = set()
    for p,q in Combinations(points,2):
        s = {p,q}
        for r in points:
            if on_same_line(p,q,r):
                s.add(r)
        lines.add(frozenset(s))

    milp = MixedIntegerLinearProgram(solver=mysolver,maximization=False)

    il = milp.new_variable(binary=True)

    # each point must be covered
    for p in points:
        milp.add_constraint( sum(il[line] for line in lines if p in line) >= 1 )
    milp.set_objective( sum(il[line] for line in lines) )

    milp.solve()

    IL = milp.get_values(il)
    Lines = sorted(sorted(line) for line in lines if IL[line])
    assert len(set.union(*map(set,Lines))) == len(points)
    return Lines


def func_grow_by_one(a_to_points, a, seq_id):
    '''
    Input: 
        `a_to_points` is a function converting initial list of terms to a list of points
        `a` is a list of initial terms
        `seq_id` is a string describing the sequence
    Extend `a` with further terms one by one.
    Prints "seq_id: n a(n)" followed by the covering lines (as lists of points).
    '''
    while True:
        Lines = min_lines(a_to_points(a))
        a.append( len(Lines) )
        print(f'{seq_id}: {len(a)-1} {a[-1]}')
        print('Lines:', Lines)
        print()
        while any( on_same_line( *line[:2], (len(a),a[-1]) ) for line in Lines ):
            a.append( len(Lines) )
            print(f'{seq_id}: {len(a)-1} {a[-1]}')
            print('Lines: same')
            print()


def func_grow_by_jumps(a_to_points, a, seq_id):
    '''
    Input: 
        `a_to_points` is a function converting initial list of terms to a list of points
        `a` is a list of initial terms
        `seq_id` is a string describing the sequence
    Extend `a` with further terms.
    Prints "seq_id: n a(n)" followed by the covering lines (as lists of points), but only for consecutive terms where value increases.
    It also prints lenghts of runs of equal values as they become known.
    '''
    while True:
        start_time = time.time()

        m = a.count(a[-1]-1)    # multiplicity of a[-1]-1
        p = a.index(a[-1])      # starting index of a[-1] in a

        # Note that we almost always have A373812(n) >= A373812(n-1) - 1. (The only known exception is n=21 with a(21) = 9 and a(20)-1 = 10.)
        a = a[:p] + m * [a[-1]]     # our starting guess is m values of a[-1]

        Lines = min_lines(a_to_points(a))
        if len(Lines)==a[-1]:
            # going up
            while len(Lines)==a[-1]:
                print('going up',a)
                a.append( len(Lines) )
                # check if the same lines cover the next term
                while any( on_same_line(*(ln:=line)[:2],(pnt:=a_to_points(a)[-1])) for line in Lines ):
                    ln.append(pnt)
                    a.append( len(Lines) )
                Lines_ = Lines
                Lines = min_lines(a_to_points(a))
        elif len(Lines) > a[-1]:
            # going down
            while len(Lines) > a[-1] + 1:
                # cut off last len(Lines) - a[-1] - 1 elements
                a = a[:a[-1]+1-len(Lines)]
                Lines = min_lines(a_to_points(a))
            assert len(Lines) == a[-1] + 1
            while True:
                print('going down',a)
                Lines_ = min_lines(a_to_points(a[:-1]))
                if len(Lines_)==a[-1]:
                    break
                Lines = Lines_
                a.pop()
        else:
            # should never happen
            raise RuntimeError

        # we have len(Lines_) == a[-1] and len(Lines) == a[-1]+1 
        print(f'{seq_id}: {len(a)-1} {a[-1]}')
        print('Lines:',Lines_,end='\n\n')

        print(f'Run of {a[-1]} has length {a.count(a[-1])}\n')

        a.append( len(Lines) )
        print(f'{seq_id}: {len(a)-1} {a[-1]}')
        print('Lines:',Lines)
        print(f'Elapsed time: {time.time()-start_time:.1f}s',end='\n\n',flush=True)


