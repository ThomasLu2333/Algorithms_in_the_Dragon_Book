from copy import deepcopy
from lexical_analysis import *


class CFG:

    # The productions need to be in a particular form where the terminals (representing the tokens) are wrapped by []
    # brackets and non-terminals by <> brackets
    def __init__(self, productions: list[str], normalize=False):
        self.productions: dict[str, list[list[str]]] = {}
        self.sigma = set()
        for production in productions:
            head, body = production.split("->")[0], production.split("->")[1]
            head = head.strip()[1:-1]
            self.productions[head] = []
            for choice in body.split("|"):
                now = ""
                symbols = []
                for c in choice.replace("", " "):
                    if c == '[' or c == '<':
                        now = ""
                    elif c == '>':
                        symbols.append(now)
                    elif c == ']':
                        symbols.append(now)
                        self.sigma.add(c)
                    elif c == EPSI:
                        symbols.append(now)
                        symbols.append(EPSI)
                        self.sigma.add(c)
                        now = ""
                    else:
                        now += c
                self.productions[head].append(symbols)
        self.symbols = list(self.productions.keys()) + list(self.sigma)
        self.id = {name: i for i, name in enumerate(list(self.productions.keys()) + list(self.sigma))}
        self.visited = dict(zip(self.symbols, [False] * len(self.id)))
        self.nullable = dict(zip(self.symbols, [False] * len(self.id)))
        self.FIRST = dict(zip(self.symbols, [set() for _ in range(len(self.id))]))
        self.FOLLOW = dict(zip(self.symbols, [set() for _ in range(len(self.id))]))
        self.resume = True
        self.start_symbol: str = list(self.productions.keys())[0]
        self.positions = dict(zip(self.symbols, [set() for _ in range(len(self.id))]))
        for head in self.productions.keys():
            for body in self.productions[head]:
                for symbol in body:
                    self.positions[symbol].add(head)
        self.set_FIRST()
        self.set_FOLLOW()

    def eliminate_epsilon_productions(self, head : str = None) -> bool:
        if head is None:
            self.visited = dict(zip(self.symbols, [False] * len(self.id)))
            return self.eliminate_epsilon_productions(self.start_symbol)

        if head in self.sigma:
            return False
        if head == EPSI:
            return True
        if self.visited[head]:
            return self.nullable[head]
        new_bodies = []
        for body in self.productions[head]:
            new_bodies.append(deepcopy(body))
            nullable_body = True
            for symbol in body:
                if not self.visited[symbol]:
                    nullable_symbol = self.eliminate_epsilon_productions(symbol)
                    if nullable_symbol:
                        for new_body in new_bodies:
                            null_new_body = deepcopy(new_body)
                            null_new_body.remove(symbol)
                            new_bodies.append(null_new_body)
                    nullable_body = nullable_body and nullable_symbol
            self.nullable[head] = self.nullable[head] or nullable_body
        self.productions[head] = list(filter(lambda x : not x and x != [], new_bodies))
        return self.nullable[head]

    def eliminate_cycles(self, head : str = None):
        if head is None:
            self.visited = dict(zip(self.symbols, [False] * len(self.id)))
            self.eliminate_cycles(self.start_symbol)
            return

        if head in self.sigma or self.visited[head]:
            return
        for body in self.productions[head]:
            for symbol in body:
                self.eliminate_cycles(symbol)
            if len(body) == 1 and body[0] not in self.sigma:
                self.productions[head].remove(body)
                for next_body in self.productions[body[0]]:
                    if len(next_body) != 1 or body[0] in self.sigma:
                        self.productions[head].append(deepcopy(next_body))


    def eliminate_left_recursion(self):
        id = {name: i for i, name in enumerate(self.productions.keys())}
        for Ai in self.productions.keys():
            for _ in range(len(self.productions[Ai])):
                body_Ai = self.productions[Ai].pop(0)
                Aj = body_Ai[0]
                if Aj not in self.sigma and id[Aj] < id[Ai]:
                    for body_Aj in self.productions[Aj]:
                        body_Ai.pop(0)
                        self.productions[Ai].append(body_Aj + body_Ai)
            Ai_prime = "__" + Ai + "'"
            self.productions[Ai_prime] = []
            for _ in range(len(self.productions[Ai])):
                body_Ai = self.productions[Ai].pop(0)
                if body_Ai[0] == Ai:
                    self.productions[Ai_prime].append(body_Ai + [Ai_prime])
                else:
                    self.productions[Ai].append(body_Ai + [Ai_prime])
            self.productions[Ai_prime].append([EPSI])

    def extract_left_factors(self):
        for head in self.productions.keys():
            pass

    def set_FIRST(self, head: str = None):

        if head is None:
            self.resume = True
            while self.resume:
                self.resume = False
                self.visited = dict(zip(self.symbols, [False] * len(self.id)))
                self.set_FIRST(self.start_symbol)

        old_size = len(self.FIRST[head])
        self.visited[head] = True
        if head in self.sigma:
            self.FIRST[head] = set(head)
        else:
            for body in self.productions[head]:
                if len(body) == 1 and body[0] == EPSI:
                    self.FIRST[head].add(EPSI)
                flag = False
                for symbol in body:
                    if not self.visited[symbol]:
                        self.set_FIRST(symbol)
                    if EPSI not in self.FIRST[symbol]:
                        self.FIRST[head] = self.FIRST[head].intersection(self.FIRST[symbol])
                        flag = True
                        break
                if not flag:
                    self.FIRST[head].add(EPSI)
        new_size = len(self.FIRST[head])
        if new_size > old_size:
            self.resume = True

    def set_FOLLOW(self, head: str = None):

        if head is None:
            self.resume = True
            self.FOLLOW[self.start_symbol].add(EPSI)
            while self.resume:
                self.resume = False
                self.visited = dict(zip(self.symbols, [False] * len(self.id)))
                for symbol in self.productions.keys():
                    if not self.visited[symbol]:
                        self.set_FOLLOW(symbol)

        self.visited[head] = True
        if head in self.sigma:
            return
        for body in self.productions[head]:
            for new_head in self.positions[head]:
                if not self.visited[new_head]:
                    self.set_FOLLOW(new_head)
            self.FOLLOW[body[-1]] = self.FOLLOW[body[-1]].union(self.FOLLOW[head])
            FIRSTs = self.FIRST[body[-1]]
            for i in range(len(body) - 2, -1, -1):
                old_size = len(self.FOLLOW[body[i]])
                self.FOLLOW[body[i]] = self.FOLLOW[body[i]].union(FIRSTs.difference({EPSI}))
                if EPSI in FIRSTs:
                    self.FOLLOW[body[i]] = self.FOLLOW[body[i]].union(self.FOLLOW[head])
                FIRSTs = FIRSTs.union(self.FIRST[body[i + 1]])
                if old_size != len(self.FOLLOW[body[i]]):
                    self.resume = True


class ParseTree:
    def __init__(self):
        pass

    def add_node(self, id, value):
        pass


class Parser:
    def __init__(self, grammar: CFG):
        raise NotImplementedError

    def set_parsing_table(self):
        raise NotImplementedError

    def parse(self, code: str, Lexer: LexicalAnalyzer) -> ParseTree:
        raise NotImplementedError


class LL1(Parser):
    pass


class SLR1(Parser):
    pass


class CLR1(Parser):
    pass


class LALR1(Parser):
    pass