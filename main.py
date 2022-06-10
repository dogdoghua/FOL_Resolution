from operator import le, ne
import sys
import re
from nltk.sem import logic, skolemize
from nltk.inference.resolution import ResolutionProverCommand

query = list()
kb = list()
expr = logic.Expression.fromstring


class SimpleSolver(object):
    def __init__(self):
        self._proof = None

    def resolution(self, predicates, target):
        conditions = [expr(i) for i in predicates]
        target = expr(target)
        negated_target = target.negate()
        predicates = conditions + [negated_target]
        clauses_set = [skolemize(i) for i in predicates]
        solver = ResolutionProverCommand(None, clauses_set)
        result = solver.prove()

        self._proof = solver.proof()

        return result

    @property
    def proof(self):
        return self._proof

    def __call__(self, *args, **kwargs):
        return self.resolution(*args, **kwargs)

def getInput():
    global kb
    global query

    n = int(input())
    for i in range(n):
        line = sys.stdin.readline().strip("\n")
        kb.append(line)
    q = int(input())
    for i in range(q):
        line = sys.stdin.readline().strip("\n")
        query.append(line)

    return kb, query


def findParenthesisDict(rule):
    stack = []
    parenthesisDict = {}
    # find corresponding right parenthesis
    for idx, ch in enumerate(rule):
        if ch == '(':
            stack.append(idx)
        elif ch == ')':
            parenthesisDict[stack.pop()] = idx
    return parenthesisDict


def addPredParenthesis(rule):
    pred = "Pred"
    tmp = ""
    index = 0
    predptr = rule.find(pred)
    if rule[predptr-1] != "(":
        rule = "(" + rule + ")"
    return rule


# check if arrow exist & replace to "~p|q" form
def removeArrow(rule):
    arrow = "=>"
    pred = "Pred"
    stack = []
    arrowIdx = findParenthesisDict(rule)
    arrowptr = rule.find(arrow)
    distance = 100
    if arrowptr > 0:
        # get the left & right parethesis 
        for l, r in arrowIdx.items():
            if l < arrowptr and arrowptr < r:
                tmp = r - l
                if distance > tmp:
                    distance = tmp
                    leftptr = l
                    rightptr = arrowIdx[leftptr]
        
        leftrule = "~(" + rule[leftptr+1:arrowptr-1] + ")"
        rightrule = rule[arrowptr+3:rightptr]
        leftrule = removeArrow(leftrule)
        rightrule = removeArrow(rightrule)
        tmp = rule[:leftptr] + leftrule + "|" + rightrule + rule[rightptr+1:]
        tmp = removeArrow(tmp)
        return tmp
    else:
        return rule


def demorgan(rule):
    tmp = ""
    idx = 0
    while idx < len(rule):
        # P => ~P
        # ~(Pred(x, y)) => Pred(x, y)
        # ~(Pred1(x) | Pred2(y)) => (P1 | P2)
        pareDict = findParenthesisDict(rule)
        if rule[idx] == "~":
            first_left_index = rule[idx:].find("(") + idx
            right_index = pareDict.get(first_left_index)    # corresponding right index to first left index
            if right_index == None: 
                print("[demorgan error] : right index is 0") 
                exit
            tmp += rule[idx+1: right_index]
            idx += (right_index - (idx+1) + 1)
        elif rule[idx] == "P":
            tmp += "~P"
        elif rule[idx] == "@":
            tmp += "#"
        elif rule[idx] == "#":
            tmp += "@"
        elif rule[idx] == "&":
            tmp += "|"
        elif rule[idx] == "|":
            tmp += "&"
        else:
            tmp += rule[idx]
        idx += 1
    return tmp


# move ~ in parenthesis
def negationInward(rule):
    pred = "Pred"
    negation = "~"
    negaptr = rule.find(negation)

    stack = []
    parenthesisIdx = findParenthesisDict(rule)
    distance = 100
    if negaptr >= 0:
        for l, r in parenthesisIdx.items():
            if l-negaptr < distance and l-negaptr>0:
                distance = l-negaptr
                leftptr = l
                rightptr = r

        predptr = rule[leftptr:rightptr].find(pred)
        predptr += leftptr
        
        if rule[negaptr+1] == "P": 
            next = rule[negaptr+1:].find(negation)
            if next>0:
                negaptr += next
                tmp = negationInward(rule[negaptr:])
            else:  # there is no ~, return rule
                return rule
        else:
            tmp = demorgan(rule[leftptr:rightptr+1])
            tmp = rule[:leftptr-1] + tmp + rule[rightptr+1:]
            
        rule = tmp
    return rule


def replaceToken(rule, token, str):
    # print("str:", str)
    # token = "@" or "#"
    # string = "all" or "exists"
    tmp = ""
    idx = 0
    # ~ P (
    # #P1 => #P2
    while idx < len(rule):
        tokenptr = rule[idx:].find(token)
        if tokenptr >= 0:
            # set tokenptr to correct global index
            tokenptr += idx
            # find first left ptr start from token
            ptrList = [rule[tokenptr + 1:].find("("), rule[tokenptr+1:].find("~"), rule[tokenptr+1:].find("P"), rule[tokenptr+1:].find("@"),
                       rule[tokenptr+1:].find("#")]
            for i in range(len(ptrList)):
                if ptrList[i] != -1:
                    ptrList[i] += tokenptr+1
            firstLeft = min(x for x in ptrList if x > 0)
            tmp += rule[idx:tokenptr]
            for i, ele in enumerate(rule[tokenptr+1:firstLeft]):
                if ele.islower():
                    tmp += str + ele + "."
            idx = firstLeft
        else:   # don't find token
            tmp += rule[idx:]
            break

    if tmp == "":
        return rule
    return tmp


def replaceExistAndAll(rule):
    tokenList = ["@", "#"]
    strList = ["all ", "exists "]

    tmp = rule
    for token, str in zip(tokenList, strList):
        tmp = replaceToken(tmp, token, str)
    return tmp


def convertToCNF(kb_list):
    for line in kb_list:
        index = kb_list.index(line)
        line = addPredParenthesis(line)
        line = removeArrow(line)
        line = negationInward(line)
        line = replaceExistAndAll(line)
        kb_list[index] = line

def main():
    result = list()
    getInput()
    print(*kb, sep="\n")
    print(*query, sep="\n")
    convertToCNF(kb)
    convertToCNF(query)
    print(*kb, sep="\n")
    print(*query, sep="\n")
    for target in query:
        solver = SimpleSolver()
        if solver(kb, target):
            result.append(1)
        else:
            result.append(0)
        print(solver.proof)
    print(result)

# Press the green button in the gutter to run the script.
if __name__ == '__main__':
    main()
