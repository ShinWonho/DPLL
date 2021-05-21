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
		print(len(cnf))
		print()
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
	def __init__(self, conflictClause):
		self.conflictClause = conflictClause
class NotDetermined(State):
	pass

def preprocess(assignment, cnf):
	for index in assignment:
		assignType = assignment.getType(index)
		if type(assignType) == Implied:
			deleteVar(cnf, index)
		else:
			break

def deleteVar(cnf, index):
	for clause in cnf:
		if index in clause:
			cnf.remove(clause)
			newClause = frozenset(set(clause).remove(index))
			if len(newClause) > 0:
				cnf.add(newClause)
		elif -index in clause:
			cnf.remove(clause)
			newClause = frozenset(set(clause).remove(-index))
			if len(newClause) > 0:
				cnf.add(newClause)

def partialAssignedCNF(assignment, cnf):
	newCNF = set()
	for clause in cnf:
		newClause = set()
		isTrue = False
		for literal in clause:
			litV = assignment.getLiteralValue(literal)
			if litV > 0:
				isTrue = True
				break
			elif litV < 0:
				continue
			else:
				newClause.add(literal)
		if isTrue:
			continue
		newCNF.add(frozenset(newClause))
	return newCNF

def DPLL(assignment, cnf):
# assignment: PartialAssigment, cnf: set of frozenset
# output: Boolean
	unitPropagation(assignment, cnf)
#preprocess(assignment, cnf)
	newCNF = partialAssignedCNF(assignment, cnf)
	state = checkSAT(assignment, newCNF)

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
		decision(assignment, newCNF)
		return (cnf, NotDetermined)
	elif state == UNSAT:
		conflictClause = getConflictClause(assignment, cnf)
		learnedClause = clauseLearning(assignment, conflictClause)
		if len(learnedClause) == 0: # TODO: revise the condition
			return (cnf, UNSAT)
		cnf.add(learnedClause)
		backTracking(assignment, cnf, learnedClause)

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
		cnf.remove(clause)
		assignment.setLiteralTrue(Implied(clause), literal)

# TODO: move this function to appropriate place
def backTracking(assignment, cnf, learnedClause):
# update assignment
# output: None
	while isCompleteClause(assignment, learnedClause):
		assignType = assignment.pop()[1][1]
		if type(assignType) == Implied:
			cnf.add(assignType.clause)
		continue

	if DEBUG:
		print("backtracking...")
		print(x)
		print(assignment)

def getConflictClause(assignment, cnf):
	for clause in cnf:
		if containBox(assignment, clause):
			return clause
	print(assignment)
	assert(False)
	

def clauseLearning(assignment, conflictClause):
# conflictClause: frozenset, output: frozenset
#			 perform clause learning and return learned clause
# output: frozen set
	if DEBUG:
		print("clause learning...")

	learnedClause = conflictClause
	for index in reversed(assignment):
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
	for clause in cnf:
		numFree = 0
		res = None
		trueClause = False
		for literal in clause:
			litV = assignment.getLiteralValue(literal)
			if litV > 0:
				trueClause = True
				break
			elif litV == 0:
				numFree += 1
				res = literal
		if trueClause:
			continue
		if numFree == 1:
			return (clause, res)
	return (None, None)
		
def checkSAT(assignment, partialCNF):
# check the satisfiability
# output: State
	if frozenset() in partialCNF:
		return UNSAT
	elif len(partialCNF) == 0:
		return SAT
	else: return NotDetermined


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

def isCompleteClause(assignment, clause):
	return len(set(map(lambda x : abs(x), clause)).difference(set(assignment.keys()))) == 0

def getFreeLiteral(assignment, clause):
# return a free literal in the clause
# output: int_opt
	result = None
	for literal in clause:
		if abs(literal) not in assignment._A: #TODO
			result = literal
		elif assignment.getLiteralValue(literal) > 0:
			return None
	return result

def decision(assignment, newCNF):
# set some free literal true
# output: None
	anyClause, *_ = newCNF
	anyLiteral, *_ = anyClause
	assignment.setLiteralTrue(Decision, anyLiteral)

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
