from lexical_analysis import *


class CFG:

    # The productions need to be in a particular form where the terminals (representing the tokens) are wrapped by []
    # brackets and non-terminals by <> brackets
    def __init__(self, productions: list[str]):
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
                        now = ""
                    else:
                        now += c
                self.productions[head].append(symbols)
        self.id = {name: i for i, name in enumerate(list(self.productions.keys()) + list(self.sigma))}
        self.visited = dict(zip(list(self.productions.keys()) + list(self.sigma), [False] * len(self.id)))
        self.FIRST = dict(zip(list(self.productions.keys()) + list(self.sigma), [set() for _ in range(len(self.id))]))
        self.FOLLOW = dict(zip(list(self.productions.keys()) + list(self.sigma), [set() for _ in range(len(self.id))]))
        self.set_FIRST()
        self.set_FOLLOW()

    def eliminate_epsilon_productions(self):
        pass

    def eliminate_cycles(self):
        pass

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
        pass

    def set_FIRST(self, head: str = None):
        if head is None:
            self.visited = dict(zip(list(self.productions.keys()) + list(self.sigma), [False] * len(self.id)))
            self.set_FIRST(list(self.productions.keys())[0])
        elif head in self.sigma:
            self.visited[head] = True
            self.FIRST[head] = set(head)
        else:
            self.visited[head] = True
            for body in self.productions[head]:
                for symbol in body:
                    if not self.visited[symbol]:
                        self.set_FIRST(symbol)
                    if EPSI not in self.FIRST[symbol]:
                        self.FIRST[head] = self.FIRST[head].intersection(self.FIRST[symbol])
                        break

    def set_FOLLOW(self, X: str = None):
        pass


class ParseTree:
    def __init__(self):
        pass

    def add_node(self, id, value):
        pass


class Parser:
    def __init__(self, grammar: CFG):
        pass

    def set_parsing_table(self):
        pass

    def parse(self, code: str, Lexer: LexicalAnalyzer) -> ParseTree:
        pass


class LL1(Parser):
    pass


class SLR1(Parser):
    pass


class CLR1(Parser):
    pass


class LALR1(Parser):
    pass
