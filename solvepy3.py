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
		(cnf, state) = DPLL(assignment, cnf)
		if state == NotDetermined:
			continue
		elif state == SAT:
			print("s SATISTFIABLE")
# TODO: print assignemnt
			break
		elif state == UNSAT:
			print("s UNSATISFIABLE")
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
		return (index, Free, 0)
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
		for index in self._A:
			assignInfo = self._A[index]
			a += str(assignInfo[0]) + "\t-> " + str(assignInfo[2]) +\
					 "\t(" + str(assignInfo[1]) + ")\n"
		return a
	def pop(self):
		return self._A.popitem()
	def append(self, element):
		self._A[element[0]] = element
	def __reversed__(self):
		return reversed(self._A)
	
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
	def __str__(self):
		return "Free"

class State(object):
	pass
class SAT(State):
	pass
class UNSAT(State):
	pass
class NotDetermined(State):
	pass

def DPLL(assignment, cnf):
# assignment: PartialAssigment, cnf: set of frozenset
# output: (cnf, State)
	performUnitPropagation(assignment, cnf)
# preprocess(assignment, cnf)
	assignedCNF = getPartialAssignedCNF(assignment, cnf)
	state = checkSAT(assignment, assignedCNF)

# Debug/Time option
	if DEBUG:
		while(input() != ""):
			continue
		print("DPLL Call")
		print("state: " + str(type(state)))
		print(assignment)
	if TIME:
		start = time.time()

	if state == SAT:
		return (cnf, SAT)
	elif state == NotDetermined:
		decision(assignment, assignedCNF)
		return (cnf, NotDetermined)
	elif state == UNSAT:
		conflictClause = getConflictClause(assignment, cnf)
		learnedClause = clauseLearning(assignment, conflictClause)
		if len(learnedClause) == 0:
			return (cnf, UNSAT)
		cnf.add(learnedClause)
		backTracking(assignment, learnedClause)

# Debug/Time option
		if DEBUG:
			print("learnedClause:")
			printClause(learnedClause)
			print()
		if TIME:
			end = time.time()
			print("conflict learning... (" + str(end - start) + "s)")

		return (cnf, NotDetermined)
	assert(False)

def performUnitPropagation(assignment, cnf):
# perform unit propagation
# output: None
	while True:
		(clause, literal) = getUnitElements(assignment, cnf)
		if clause == None:
			break
		assignment.setLiteralTrue(Implied(clause), literal)

# TODO: make general form of iterate the unassigned CNF
def getUnitElements(assignment, cnf):
# if unit clause exist, return the literal and clause
# output: (frozenset_opt, int_opt)
	for clause in cnf:
		numFree = 0
		res = None
		isTrueClause = False
		for literal in clause:
			literalValue = assignment.getLiteralValue(literal)
			if literalValue > 0:
				isTrueClause = True
				break
			elif literalValue == 0:
				numFree += 1
				res = literal
		if isTrueClause:
			continue
		if numFree == 1:
			return (clause, res)
	return (None, None)

def getPartialAssignedCNF(assignment, cnf):
# assign the value to the cnf
# it returns the assignedCNF
# output: set of frozenset
	assignedCNF = set()
	for clause in cnf:
		newClause = set()
		isTrueClause = False
		for literal in clause:
			literalValue = assignment.getLiteralValue(literal)
			if literalValue > 0:
				isTrueClause = True
				break
			elif literalValue < 0:
				continue
			else:
				newClause.add(literal)
		if isTrueClause:
			continue
		assignedCNF.add(frozenset(newClause))
	return assignedCNF
		
def checkSAT(assignment, assignedCNF):
# check the satisfiability
# output: State
	if frozenset() in assignedCNF:
		return UNSAT
	elif len(assignedCNF) == 0:
		return SAT
	else: return NotDetermined

def decision(assignment, cnf):
# set some free literal true
# output: None
	anyClause, *_ = cnf
	anyLiteral, *_ = anyClause
	assignment.setLiteralTrue(Decision, anyLiteral)

	if DEBUG:
		print("decision...")
		print(anyLiteral)
		print()

def getConflictClause(assignment, cnf):
# given the assignment, get any conflict clause in the cnf
# output: frozeset
	for clause in cnf:
		if isBox(assignment, clause):
			return clause
	print(assignment)
	assert(False)
	
def isBox(assignment, clause):
# check if the clause contains box
# output: Boolean
	for literal in clause:
		if assignment.getLiteralValue(literal) >= 0:
			return False
	return True

def clauseLearning(assignment, conflictClause):
#	perform clause learning and return learned clause
# output: frozen set
	if DEBUG:
		print("clause learning...")

	learnedClause = conflictClause
	for index in reversed(assignment):
		assignType = assignment.getType(index)
		if (type(assignType) == Implied
				and -index * assignment[index] in learnedClause):
			learnedClause = resolventOf(set(learnedClause),
					set(assignType.clause), index)

			if DEBUG:
				printClause(learnedClause)
				print()

	return learnedClause

def resolventOf(c1, c2, index):
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

def backTracking(assignment, learnedClause):
# update assignment
# output: None
	while True:
		index = assignment.pop()[0]
		if index in learnedClause or -index in learnedClause:
			break

	if DEBUG:
		print("backtracking...")
		print(assignment)

################################################################

# Not Used in this version

def _isTrueClause(assignment, clause):
# check whether the cluase is true
# output: Boolean
	for literal in clause:
		if assignment.getLiteralValue(literal) > 0:
			return True
	return False

def _isCompleteClause(assignment, clause):
	return len(set(map(lambda x : abs(x), clause)).difference(set(assignment.keys()))) == 0

def _getFreeLiteral(assignment, clause):
# return a free literal in the clause
# output: int_opt
	result = None
	for literal in clause:
		if abs(literal) not in assignment._A: #TODO
			result = literal
		elif assignment.getLiteralValue(literal) > 0:
			return None
	return result

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
