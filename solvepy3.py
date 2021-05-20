import argparse
import time
from collections import OrderedDict

DEBUG = False
TIME = False

def parseClause(line):
# line: a clause of CNF in string format
#				last two element of the line indicates
#				the end of the clause: "0", "\n"
#				parse the string into set of literals
# output: set of int
	return frozenset(map(int,line[:-2].split()))

def processFile(lines):
# lines: the lines of file
# 			 process it to CNF form
# output: tuple(cnf, nvar, nclause)
	i = 0
	while (lines[i][0] == 'c'):
		i += 1

	info = lines[i].split()
	i += 1
	nvar = int(info[2])
	nclause = int(info[3])

	cnf = set(map(parseClause, lines[i:i+nclause]))

	if DEBUG:
		printCNF(cnf)

	maxIndex = 0
	for clause in cnf:
		for literal in clause:
			if abs(literal) > maxIndex: maxIndex = abs(literal)

	assert(maxIndex == nvar)
	return (cnf, nvar, nclause)

def getCNF(fname):
# fname: file name of .cnf file
# 			get and process the file into CNF form
# output: tuple(cnf, nvar, nclause)
	if DEBUG:
		print("File: " + fname)
		print()

	f = open(fname, 'r')
	lines = f.readlines()
	return processFile(lines)

def main():
	start = time.time()
	parser = argparse.ArgumentParser()
	parser.add_argument('X')
	args = parser.parse_args()
	(cnf, nvar, nclause) = getCNF(args.X)
	assignment = PartialAssignment()
	end = time.time()
	while True:
		print(len(assignment._A))
		(cnf, state) = DPLL(assignment, cnf)
		if state == NotDetermined:
			continue
		elif state == SAT:
			print("SAT")
			break
		elif state == UNSAT:
			print("UNSAT")
			break
		else:
		 	assert(False)

################################################################

# DPLL algorithm

# partial assignment
# element of PartialAssignment:
#		index -> (index of variable, type of assignment, value)
# -1 stands for false, 1 stands for true

# TODO: changed data structure more elastic form
class PartialAssignment(object):
	def __init__(self):
		self._A = OrderedDict()
	def _getElement(self, literal):
		index = abs(literal)
		if index in self._A:
			return self._A[index]
		return (index, Free(), 0)
	def __setitem__(self, index, typeAndValue):
		assert(index > 0)
		self._A[index] = (index, typeAndValue[0], typeAndValue[1])
	def __getitem__(self, literal):
		return self._getElement(literal)[2]
	def getType(self, literal):
		return self._getElement(literal)[1]
	def setLiteralTrue(self, assignType, literal):
		if literal > 0:
			self._A[literal] = (literal, assignType, 1)
		else:
			self._A[-literal] = (-literal, assignType, -1)
	def keys(self):
		return list(self._A.keys())
	def getLiteralValue(self, literal):
		return self[literal] * literal
	def __str__(self):
		a = "<Partial Assignment>\n"
		for assignInfo in self._A:
			a += str(assignInfo[0]) + "\t-> " + str(assignInfo[2]) +\
					 "\t(" + str(assignInfo[1]) + ")\n"
		return a
	def pop(self):
		return self._A.popitem()
	def append(self, element):
		self._A[element[0]] = element
	
class AssignmentType(object):
	pass
class Implied(AssignmentType):
	def __init__(self, clause):
		self.clause = clause
	def __str__(self):
		return "Implied"
class Decision(AssignmentType):
	def __str__(self):
		return "Decision"
class Free(AssignmentType):
	def __str(self):
		return "Free"

class State(object):
	pass
class SAT(State):
	pass
class UNSAT(State):
	def __init__(self, conflictClause):
		self.conflictClause = conflictClause
class NotDetermined(State):
	pass

def DPLL(assignment, cnf):
# assignment: PartialAssigment, cnf: set of frozenset
# output: Boolean
	unitPropagation(assignment, cnf)
	state = checkSAT(assignment, cnf)

	if DEBUG:
		while(input() != ""):
			continue
		print("DPLL Call")
		print("state: " + str(type(state)))
		print(assignment)
	if TIME:
		start = time.time()

	if type(state) == SAT:
		return (cnf, SAT)
	elif type(state) == NotDetermined:
		decision(assignment, cnf)
		return (cnf, NotDetermined)
	elif type(state) == UNSAT:
		learnedClause = clauseLearning(assignment,
				state.conflictClause)
		if len(learnedClause) == 0: # TODO: revise the condition
			return (cnf, UNSAT)
		cnf.add(learnedClause)
		backTracking(assignment, learnedClause)

		if DEBUG:
			print("learnedClause:")
			printClause(learnedClause)
			print()
		if TIME:
			end = time.time()
			print("conflict learning... (" + str(end - start) + "s)")

		return (cnf, NotDetermined)
	assert(False)

def unitPropagation(assignment, cnf):
# perform unit propagation
# output: None
	while True:
		(clause, literal) = getUnitElements(assignment, cnf)
		if clause == None:
			break
		assignment.setLiteralTrue(Implied(clause), literal)

# TODO: move this function to appropriate place
def backTracking(assignment, learnedClause):
# update assignment
# output: None
	while (x := getFreeLiteral(assignment, learnedClause)) == None:
		assignment.pop()
		continue

	if DEBUG:
		print("backtracking...")
		print(x)
		print(assignment)
	

def clauseLearning(assignment, conflictClause):
# conflictClause: frozenset, output: frozenset
#			 perform clause learning and return learned clause
# output: frozen set
	if DEBUG:
		print("clause learning...")

	learnedClause = conflictClause
	indices = assignment.keys()
	indices.reverse()
	for index in indices:
		assignType = assignment.getType(index)
		if (type(assignType) == Implied
				and -index * assignment[index] in learnedClause):
			learnedClause = resolvent(set(learnedClause),
					set(assignType.clause), index)

			if DEBUG:
				printClause(learnedClause)
				print()

	return learnedClause

def resolvent(c1, c2, index):
# c1: set, c2: set, index: int
# perform resolvent of c1 and c2 respect to index
# output: frozenset
	if DEBUG:
		print("resolution respect to " + str(index) + "...")
		printClause(c1)
		printClause(c2)
		print()

	if index in c2:
		index = -index
	c1.remove(index)
	c2.remove(-index)
	return frozenset(c1.union(c2))

def getUnitElements(assignment, cnf):
# if unit clause exist, return the literal and clause
# output: (frozenset_opt, int_opt)
	boundVars = set(assignment.keys())
	possibleLiterals = boundVars.union(
			set(map(lambda x : -x, boundVars)))
	for clause in cnf:
		if isTrueClause(assignment, clause):
			continue
		remaingLiteral = clause.difference(possibleLiterals)
		if len(remaingLiteral) == 1:
			literal, *_ = remaingLiteral
			return (clause, literal)
	return (None, None)
		
def checkSAT(assignment, cnf):
# check the satisfiability
# output: State
	complete = True
	for clause in cnf:
		for literal in clause:
			if getFreeLiteral(assignment, clause) != None:
				complete = False
			if containBox(assignment, clause):
				return UNSAT(clause)
	if complete:
		return SAT()
	else:
		return NotDetermined()

def isTrueClause(assignment, clause):
	for literal in clause:
		if assignment.getLiteralValue(literal) > 0:
			return True
	return False

def containBox(assignment, clause):
# check if the clause contains box
# output: Boolean
	for literal in clause:
		if assignment.getLiteralValue(literal) >= 0:
			return False
	return True

def getFreeLiteral(assignment, clause):
# return a free literal in the clause
# output: int_opt
	for literal in clause:
		if assignment.getLiteralValue(literal) == 0:
			return literal
	return None

def decision(assignment, cnf):
# set some free literal true
# output: None
	for clause in cnf:
		literal = getFreeLiteral(assignment, clause)
		if literal != None:
			assignment.setLiteralTrue(Decision(), literal)
			break

	if DEBUG:
		print("decision...")
		print(literal)
		print()

################################################################

# Helper Functions

def printCNF(cnf):
# cnf: set of sets of int
# 		 it prints the CNF
# output: None
	print("CNF formula is the following:")
	for clause in cnf:
		printClause(clause)
	print()

def printClause(clause):
	x = ""
	for literal in clause:
		index = abs(literal)
		if index > literal: x += "¬"
		x += "x" + str(index) + "\t"
	print(x)


if __name__ == "__main__":
	main()
