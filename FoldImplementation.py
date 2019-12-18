#!/usr/bin/env python
# coding: utf-8
from ast import literal_eval
import numpy as np

ab = 0
goal = "fly"
exceptions = []

class Rule():
    def __init__(self, head, body):
        self.head = head
        self.body = body

class Fact():
    def __init__(self, predicate, values):
        self.predicate = predicate
        self.values = values

class BackgroundKnowledge():
    def __init__(self, rules, facts):
        self.rules = rules
        self.facts = facts

rules = [Rule("bird", ["penguin"])]
facts = [Fact("bird", "tweety"), Fact("bird", "et"), Fact("cat", "kitty"), Fact("penguin", "polly")]
pExamples = ["tweety", "et"]
nExamples = ["kitty", "polly"]
predicates = ["bird", "cat", "penguin"]

def Fold(pExamples, nExamples, predicates, backgroundKnowledge):
    global goal
    global exceptions
    defaultRules = []
    while (len(pExamples) > 0):
        c = Rule(goal, [])
        c_new = specialize(c, pExamples, nExamples, predicates, backgroundKnowledge)
        pExamples = removeCovers(c_new, pExamples, backgroundKnowledge)
        defaultRules.append(c_new)
        defaultRules, exceptions = updateRulesExceptions(defaultRules, exceptions, backgroundKnowledge)
    return defaultRules, exceptions

def specialize(c, pExamples, nExamples, predicates, backgroundKnowledge):
    c_new = c

    c_def, IG = addBestLiteral(c_new, pExamples, nExamples, predicates, backgroundKnowledge)
    if c_def == 0:
        c_new = Rule(c.head, [str(pExamples)])
    else:
        c_new = c_def
        predicates.remove(c_new.body[0])
    for ex in exceptions:
        exception_present = False
        for rules in backgroundKnowledge.rules:
            if ex.head == rules.head and ex.body == rules.body:
                exception_present = True
                break
        if exception_present == False:
            backgroundKnowledge.rules.append(ex)

    pExamples = removeCovers(c_new, pExamples, backgroundKnowledge)
    nExamples = covers(c_new, nExamples, backgroundKnowledge)[1]

    while len(nExamples)>0:
        c_def, IG = addBestLiteral(c_new, pExamples, nExamples, predicates, backgroundKnowledge)
        if c_def != 0:
            c_new = c_def
            predicates.remove(c_new.body[0])
        else:
            c_new = exception(c_new, nExamples, pExamples, predicates, backgroundKnowledge)
            if c_new == 0:
                c_new = Rule(c.head, [str(pExamples)])
        for ex in exceptions:
            exception_present = False
            for rules in backgroundKnowledge.rules:
                if ex.head == rules.head and ex.body == rules.body:
                    exception_present = True
                    break
            if exception_present == False:
                backgroundKnowledge.rules.append(ex)

        pExamples = removeCovers(c_new, pExamples, backgroundKnowledge)
        nExamples = covers(c_new, nExamples, backgroundKnowledge)[1]
    return c_new


def exception(c, pExamples, nExamples, predicates, backgroundKnowledge):
    global exceptions
    c_def, IG = addBestLiteral(c, pExamples, nExamples, predicates, backgroundKnowledge)
    if (c_def != 0):
        c_set = Fold(pExamples, nExamples, predicates, backgroundKnowledge)[0]
        c_ab = generateNextAbPredicate()
        for var in c_set:
            exceptions.append(Rule(c_ab, var.body))
        c_new = Rule(c_def.head, c.body + ["-" + c_ab])
    else:
        c_new = 0
    return c_new

def removeCovers(c_new, pExamples, backgroundKnowledge):
    coveredEx = []
    result = []
    for ex in pExamples:
        if helper(c_new, ex, backgroundKnowledge):
            coveredEx.append(ex)
    for elem in pExamples:
        if elem not in coveredEx:
            result.append(elem)
    return list(result)

def updateRulesExceptions(defaultRules, exceptions, backgroundKnowledge):
    for ex in exceptions:
        exception_present = True
        for bk in backgroundKnowledge.rules:
            if not ex.head == bk.head and ex.body == bk.body:
                exception_present = False
                break
        if exception_present == False:
            backgroundKnowledge.rules.append(ex)

    for rules in defaultRules:
        rules_present = True
        for bk in backgroundKnowledge.rules:
            if not rules.head == bk.head and rules.body == bk.body:
                rules_present = False
                break
        if rules_present == False:
            backgroundKnowledge.rules.append(rules)
        for bk in rules.body:
            if bk in predicates:
                predicates.remove(bk)
    return defaultRules, exceptions

def covers(c_new, examples, backgroundKnowledge):
    coveredExamples = []
    i = 0
    coverLength = 0
    while i < len(examples):
        if helper(c_new, examples[i], backgroundKnowledge):
            coveredExamples.append(examples[i])
            coverLength += 1
        i+=1
    return coverLength, coveredExamples

def helper(rule, example, backgroundKnowledge):
    for clause in rule.body:
        #Negative Clauses
        if clause[0] == '-':
            if clause[1] == '[':
                literal_clause = literal_eval(clause[1:])
                if example in literal_clause:
                    return False
            else:
                clause = clause[1:]
                for fact in backgroundKnowledge.facts:
                    if fact.predicate == clause and fact.values == example:
                        return False
                for rule in backgroundKnowledge.rules:
                    if rule.head == clause and helper(rule, example, backgroundKnowledge):
                        return False
                return True
        #Positive Clauses
        else:
            if clause[0] == '[':
                literal_clause = literal_eval(clause[1:])
                if example not in literal_clause:
                    return False

            present = False
            for fact in backgroundKnowledge.facts:
                if fact.predicate == clause and fact.values == example:
                    present = True
                    break
            for rule in backgroundKnowledge.rules:
                if rule.head == clause and helper(rule, example, backgroundKnowledge):
                    present = True
                    break
            if present == True:
                continue
            return False
    return True

def generateNextAbPredicate():
    global ab
    new_ab = "ab" + str(ab)
    ab = ab + 1
    return new_ab

def addBestLiteral(c, pExamples, nExamples, predicates, backgroundKnowledge):
    rules = dict()
    IGs = dict()
    nR = covers(c, nExamples, backgroundKnowledge)[0]
    pR = covers(c, pExamples, backgroundKnowledge)[0]
    i = 0
    while i < len(predicates):
        pred = predicates[i]
        i = i+1
        tempBody = list(c.body)
        tempBody.append(pred)
        pRL = covers(Rule(c.head, tempBody), pExamples, backgroundKnowledge)[0]
        nRL = covers(Rule(c.head, tempBody), nExamples, backgroundKnowledge)[0]

        if pRL == 0 or pR == 0:
            continue

        IG = float(pRL) * (np.log2(float(pRL) / (float(pRL) + float(nRL))) - np.log2(float(pR) / (float(pR) + float(nR))))
        if IG < 0:
            continue
        rules[pred] = Rule(c.head, tempBody)
        IGs[pred] = IG

    if len(IGs.keys()) == 0:
        return 0, 0
    best_pred = max(IGs.items(), key=lambda x: x[1])
    return rules[best_pred[0]], IGs[best_pred[0]]

def output(result):
    for rule in result:
        print(rule[0].head + ":-"),
        for x in rule[0].body:
            print(" " + str(x))
    return

result = Fold(pExamples, nExamples, predicates, BackgroundKnowledge(rules, facts))
output(result)