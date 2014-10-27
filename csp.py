#!/usr/bin/python
# -*- coding: utf-8 -*-

import copy
import itertools
import random

class CSP:    
    def __init__(self):
        # self.variables is a list of the variable names in the CSP
        self.variables = []

        # self.domains[i] is a list of legal values for variable i
        self.domains = {}

        # self.constraints[i][j] is a list of legal value pairs for
        # the variable pair (i, j)
        self.constraints = {}
        
        # Backtrack numbers
        self.backtrack_called = 0
        self.backtrack_failed = 0

    def add_variable(self, name, domain):
        """Add a new variable to the CSP. 'name' is the variable name
        and 'domain' is a list of the legal values for the variable.
        """
        
        self.variables.append(name)
        self.domains[name] = list(domain)
        self.constraints[name] = {}

    def get_all_possible_pairs(self, a, b):
        """Get a list of all possible pairs (as tuples) of the values in
        the lists 'a' and 'b', where the first component comes from list
        'a' and the second component comes from list 'b'.
        """
        
        return itertools.product(a, b)

    def get_all_arcs(self):
        """Get a list of all arcs/constraints that have been defined in
        the CSP. The arcs/constraints are represented as tuples (i, j),
        indicating a constraint between variable 'i' and 'j'.
        """
        
        return [ (i, j) for i in self.constraints for j in self.constraints[i] ]

    def get_all_neighboring_arcs(self, var):
        """Get a list of all arcs/constraints going to/from variable
        'var'. The arcs/constraints are represented as in get_all_arcs().
        """
        
        return [ (i, var) for i in self.constraints[var] ]

    def add_constraint_one_way(self, i, j, filter_function):
        """Add a new constraint between variables 'i' and 'j'. The legal
        values are specified by supplying a function 'filter_function',
        that returns True for legal value pairs and False for illegal
        value pairs. This function only adds the constraint one way,
        from i -> j. You must ensure that the function also gets called
        to add the constraint the other way, j -> i, as all constraints
        are supposed to be two-way connections!
        """
        
        if not j in self.constraints[i]:
            # First, get a list of all possible pairs of values between variables i and j
            self.constraints[i][j] = self.get_all_possible_pairs(self.domains[i], self.domains[j])

        # Next, filter this list of value pairs through the function
        # 'filter_function', so that only the legal value pairs remain
        self.constraints[i][j] = filter(lambda value_pair: filter_function(*value_pair), self.constraints[i][j])

    def add_all_different_constraint(self, variables):
        """Add an Alldiff constraint between all of the variables in the
        list 'variables'.
        """
        for (i, j) in self.get_all_possible_pairs(variables, variables):
            if i != j:
                self.add_constraint_one_way(i, j, lambda x, y: x != y)

    def backtracking_search(self):
        """This functions starts the CSP solver and returns the found
        solution.
        """
        
        # Make a so-called "deep copy" of the dictionary containing the
        # domains of the CSP variables. The deep copy is required to
        # ensure that any changes made to 'assignment' does not have any
        # side effects elsewhere.
        assignment = copy.deepcopy(self.domains)

        # Run AC-3 on all constraints in the CSP, to weed out all of the
        # values that are not arc-consistent to begin with
        self.inference(assignment, self.get_all_arcs())

        # Call backtrack with the partial assignment 'assignment'
        return self.backtrack(assignment)

    def backtrack(self, assignment):
        """The function 'Backtrack' from the pseudocode in the
        textbook.

        The function is called recursively, with a partial assignment of
        values 'assignment'. 'assignment' is a dictionary that contains
        a list of all legal values for the variables that have *not* yet
        been decided, and a list of only a single value for the
        variables that *have* been decided.

        When all of the variables in 'assignment' have lists of length
        one, i.e. when all variables have been assigned a value, the
        function should return 'assignment'. Otherwise, the search
        should continue. When the function 'inference' is called to run
        the AC-3 algorithm, the lists of legal values in 'assignment'
        should get reduced as AC-3 discovers illegal values.

        IMPORTANT: For every iteration of the for-loop in the
        pseudocode, you need to make a deep copy of 'assignment' into a
        new variable before changing it. Every iteration of the for-loop
        should have a clean slate and not see any traces of the old
        assignments and inferences that took place in previous
        iterations of the loop.
        """
        
        # Increase backtrack_called
        self.backtrack_called += 1
        
        finished = True
        for a in assignment:
            if len(assignment[a]) > 1:
                finished = False
                break
        
        if finished:
            return assignment
        else:
            debug_print(assignment)
            var = self.select_unassigned_variable(assignment)
            for value in self.domains[var]:
                new_assignment = copy.deepcopy(assignment)
                # Test 123
                new_assignment[var] = [value]
                inference = self.inference(new_assignment, self.get_all_arcs())
                if inference is not False:
                    result = self.backtrack(new_assignment)
                    if result is not False:
                        return result
                
                for idx, a in enumerate(assignment[var]):
                    if a is value:
                        del assignment[var][idx]
                        break
                
                
        self.backtrack_failed += 1
        return False

    def select_unassigned_variable(self, assignment):
        """The function 'Select-Unassigned-Variable' from the pseudocode
        in the textbook. Should return the name of one of the variables
        in 'assignment' that have not yet been decided, i.e. whose list
        of legal values has a length greater than one.
        """
        
        unassigned = []
        for a in assignment:
            if len(assignment[a]) > 1:
                unassigned.append(a)
        
        return random.choice(unassigned)

    def inference(self, assignment, queue):
        """The function 'AC-3' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'queue'
        is the initial queue of arcs that should be visited.
        """
        
        while len(queue) > 0:
            (i, j) = queue.pop(0)
            if self.revise(assignment, i, j):
                if len(self.domains.get(i)) == 0:
                    return False
                for k in self.get_all_neighboring_arcs(i):
                    if cmp(k, (i, j)) is not 0:
                        queue.append(k)
                
        return True
        
    def revise(self, assignment, i, j):
        """The function 'Revise' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'i' and
        'j' specifies the arc that should be visited. If a value is
        found in variable i's domain that doesn't satisfy the constraint
        between i and j, the value should be deleted from i's list of
        legal values in 'assignment'.
        """
        
        revised = False
        for x in self.domains.get(i):
            found = False
            for y in self.domains.get(j):
                if (x, y) in self.constraints.get(i).get(j):
                    found = True
                    break
            
            if found is False:
                for key, d in enumerate(self.domains.get(i)):
                    if d == x:
                        del self.domains.get(i)[key]
                revised = True
        return revised
        
        

def create_map_coloring_csp():
    """Instantiate a CSP representing the map coloring problem from the
    textbook. This can be useful for testing your CSP solver as you
    develop your code.
    """
    
    csp = CSP()
    states = [ 'WA', 'NT', 'Q', 'NSW', 'V', 'SA', 'T' ]
    edges = { 'SA': [ 'WA', 'NT', 'Q', 'NSW', 'V' ], 'NT': [ 'WA', 'Q' ], 'NSW': [ 'Q', 'V' ] }
    colors = [ 'red', 'green', 'blue' ]
    for state in states:
        csp.add_variable(state, colors)
    for state, other_states in edges.items():
        for other_state in other_states:
            csp.add_constraint_one_way(state, other_state, lambda i, j: i != j)
            csp.add_constraint_one_way(other_state, state, lambda i, j: i != j)
    return csp

def create_sudoku_csp(filename):
    """Instantiate a CSP representing the Sudoku board found in the text
    file named 'filename' in the current directory.
    """
    
    csp = CSP()
    board = map(lambda x: x.strip(), open(filename, 'r'))

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                csp.add_variable('%d-%d' % (row, col), map(str, range(1, 10)))
            else:
                csp.add_variable('%d-%d' % (row, col), [ board[row][col] ])

    for row in range(9):
        csp.add_all_different_constraint([ '%d-%d' % (row, col) for col in range(9) ])
    for col in range(9):
        csp.add_all_different_constraint([ '%d-%d' % (row, col) for row in range(9) ])
    for box_row in range(3):
        for box_col in range(3):
            cells = []
            for row in range(box_row * 3, (box_row + 1) * 3):
                for col in range(box_col * 3, (box_col + 1) * 3):
                    cells.append('%d-%d' % (row, col))
            csp.add_all_different_constraint(cells)

    return csp

def debug_print(solution):
    for i in range(9):
        output = ''
        for j in range(9):
            values = solution[str(i) + "-" + str(j)]
            if len(values) == 1:
                output += " " + values[0] + " "
            else:
                output += "   "
            
            if j == 2 or j == 5:
                output += "|"
        print output
        if i == 2 or i == 5:
            print '---------+---------+---------'
    print " "
    print " "

def debug_information(csp):
    # Return debug information
    print " "
    print "Backtrack was called \033[91m" + str(csp.backtrack_called) + "\033[0m times."
    print "Backtrack returned false \033[91m" + str(csp.backtrack_failed) + "\033[0m times."

def ask():
    # Loop until we have a real answer
    while True:
        # Print question
        print "Enter 1-4 on your keyboard to decide difficulity:"
        print " "
        
        # Print options
        print "\033[91m1.\033[0m Easy"
        print "\033[91m2.\033[0m Medium"
        print "\033[91m3.\033[0m Hard"
        print "\033[91m4.\033[0m Very hard"
        print " "
        
        # Get input
        try:
            # Ask user
            ipt = str(input("Enter 1-4 value for map: "))
            
            # Try to parse
            val = int(ipt)
            
            # Check valid number
            if val >= 1 and val <= 4:
                return val
        except Exception:
            # Just pass here
            pass
        
        # Print angry error message
        print " "
        print "\033[91m═══════════════════════════════════════════════════════════════════════════\033[0m"
        print " "

def main():
    # Maps
    maps = ['easy', 'medium', 'hard', 'veryhard']
    
    # Find what problem to solve
    difficulity = ask()
    
    # Create new csp
    csp = create_sudoku_csp('sudokus/' + maps[difficulity - 1] + '.txt')
    
    # Start backtracking
    result = csp.backtracking_search()
    
    # Print out the final output
    debug_print(result)
    
    # Print debug information
    debug_information(csp)

if __name__ == "__main__":
    # Running main
    main()
    