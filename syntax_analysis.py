from copy import deepcopy
from lexical_analysis import *


class CFG:

    # The productions need to be in a particular form where the terminals (representing the tokens) are wrapped by []
    # brackets and non-terminals by <> brackets
    def __init__(self, raw_productions: list[str], augment: bool = False):
        self.raw_productions = raw_productions
        self.productions: dict[str, list[list[str]]] = {}
        self.sigma = set()
        for production in raw_productions:
            head, body = production.split("::=")[0], production.split("::=")[1]
            head = head.strip()[1:-1]
            self.productions[head] = []
            for choice in body.split("|"):
                now = ""
                symbols = []
                for c in choice.replace(" ", ""):
                    if c == '[' or c == '<':
                        now = ""
                    elif c == '>':
                        symbols.append(now)
                    elif c == ']':
                        symbols.append(now)
                        self.sigma.add(now)
                    elif c == EPSI:
                        if now != "":
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

    def eliminate_epsilon_productions(self, head: str = None) -> bool:
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
        self.productions[head] = list(filter(lambda x: not x and x != [], new_bodies))
        return self.nullable[head]

    def eliminate_cycles(self, head: str = None):
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
        for Ai in list(self.productions.keys()):
            for _ in range(len(self.productions[Ai])):
                body_Ai = self.productions[Ai].pop(0)
                Aj = body_Ai[0]
                if Aj not in self.sigma and id[Aj] < id[Ai]:
                    body_Ai.pop(0)
                    for body_Aj in self.productions[Aj]:
                        self.productions[Ai].append(body_Aj + body_Ai)
                else:
                    self.productions[Ai].append(body_Ai)
            Ai_prime = "__" + Ai + "'"
            self.productions[Ai_prime] = []
            for _ in range(len(self.productions[Ai])):
                body_Ai = self.productions[Ai].pop(0)
                if body_Ai[0] == Ai:
                    body_Ai.pop(0)
                    self.productions[Ai_prime].append(body_Ai + [Ai_prime])
                else:
                    self.productions[Ai].append(body_Ai + [Ai_prime])
            self.productions[Ai_prime].append([EPSI])
        return

    # TODO: this function only eliminates left factors that directly affect parsing. Need to amend this function to
    #  eliminate all left factors
    def extract_left_factors(self):
        for head in list(self.productions.keys()):
            max_len = max([len(body) for body in self.productions[head]]) + 1
            partitions = [self.productions[head]]
            for i in range(max_len):
                new_partitions = []
                new_partition_dict = {}
                matches = []
                for partition in partitions:
                    for body in partition:
                        if i <= len(body) - 1:
                            if not new_partition_dict.get(body[i]):
                                new_partition_dict[body[i]] = []
                            new_partition_dict[body[i]].append(body)
                        else:
                            matches.append(body)
                    for new_partition in new_partition_dict.values():
                        if len(new_partition) == 1:
                            matches.append(new_partition[0])
                        else:
                            new_partitions.append(new_partition)
                    if i != 0 and matches:
                        left_factor = matches[0][:i]
                        left_factor_name = ",".join(left_factor)
                        self.productions[left_factor_name] = [left_factor]
                        for body in matches:
                            del body[:i]
                            body.insert(0, left_factor_name)
                partitions = new_partitions

    def set_FIRST(self, head: str = None):

        if head is None:
            self.resume = True
            while self.resume:
                self.resume = False
                self.visited = dict(zip(self.symbols, [False] * len(self.id)))
                for symbol in self.symbols:
                    if not self.visited[symbol]:
                        self.set_FIRST(symbol)
            return

        old_size = len(self.FIRST[head])
        self.visited[head] = True
        if head in self.sigma:
            self.FIRST[head] = {head}
        else:
            for body in self.productions[head]:
                if len(body) == 1 and body[0] == EPSI:
                    self.FIRST[head].add(EPSI)
                flag = False
                for symbol in body:
                    if not self.visited[symbol]:
                        self.set_FIRST(symbol)
                    self.FIRST[head] = self.FIRST[head].union(self.FIRST[symbol].difference({EPSI}))
                    if EPSI not in self.FIRST[symbol]:
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
            self.FOLLOW[self.start_symbol].add(END_OF_STRING)
            while self.resume:
                self.resume = False
                self.visited = dict(zip(self.symbols, [False] * len(self.id)))
                for symbol in self.symbols:
                    if not self.visited[symbol]:
                        self.set_FOLLOW(symbol)
            return

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
                if EPSI in self.FIRST[body[i]] and EPSI in FIRSTs:
                    FIRSTs = FIRSTs.union(self.FIRST[body[i]])
                elif EPSI in self.FIRST[body[i]]:
                    FIRSTs = FIRSTs.union(self.FIRST[body[i]].difference({EPSI}))
                else:
                    FIRSTs = self.FIRST[body[i]]
                if EPSI in FIRSTs:
                    self.FOLLOW[body[i]] = self.FOLLOW[body[i]].union(self.FOLLOW[head])
                if old_size != len(self.FOLLOW[body[i]]):
                    self.resume = True


class ParseTree:
    def __init__(self, grammar: CFG, root = None):
        self.grammar = grammar
        self.root = root
        self.values: list[str | Token] = []
        self.next_node = 0
        self.children: list[list[int]] = []

    def add_node(self, value: str | Token, father: int = None) -> int:
        self.values.append(value)
        self.children.append([])
        if father is not None:
            self.children[father].append(self.next_node)
        self.next_node += 1
        return self.next_node - 1

    def set_root(self, x):
        self.root = x



class Parser:
    def __init__(self, grammar: CFG):
        self.grammar = grammar

    def set_parsing_table(self):
        raise NotImplementedError

    def parse(self, code: str, Lexer: LexicalAnalyzer) -> ParseTree:
        raise NotImplementedError


class LL1(Parser):
    def __init__(self, grammar: CFG, normalize=True):
        super().__init__(grammar)
        if normalize:
            grammar.eliminate_epsilon_productions()
            grammar.eliminate_cycles()
            grammar.eliminate_left_recursion()
            grammar.extract_left_factors()
            grammar.set_FIRST()
            grammar.set_FOLLOW()
        self.M: dict[tuple[str, str], None | list[str]] = {}
        for head in self.grammar.productions.keys():
            for nonterminal in self.grammar.sigma:
                self.M[head, nonterminal] = None
            self.M[head, END_OF_STRING] = None
        self.set_parsing_table()

    def set_parsing_table(self):
        for A in self.grammar.productions.keys():
            for α in self.grammar.productions[A]:
                for a in self.grammar.FIRST[A]:
                    if a in self.grammar.sigma and a != EPSI:
                        if self.M[A, a] is not None:
                            raise ValueError("The grammar is not LL(1)")
                        self.M[A, a] = α
                flag = True
                for symbol in α:
                    if EPSI not in self.grammar.FIRST[symbol]:
                        flag = False
                        break
                if flag:
                    for b in self.grammar.FOLLOW[A]:
                        if b in self.grammar.sigma:
                            if self.M[A, b] is not None:
                                raise ValueError("The grammar is not LL(1)")
                            self.M[A, b] = α
                if flag and END_OF_STRING in self.grammar.FOLLOW[A]:
                    if self.M[A, END_OF_STRING] is not None:
                        raise ValueError("The grammar is not LL(1)")
                    self.M[A, END_OF_STRING] = α

    def parse(self, code: str, Lexer: LexicalAnalyzer) -> ParseTree:
        T = ParseTree(self.grammar)
        T.set_root(0)
        T.add_node(self.grammar.start_symbol)
        Lexer.set_input(code)
        Stack: list[str] = [self.grammar.start_symbol]
        TreeNodes = [0]
        a = Lexer.get_next_token()
        while Stack:
            X = Stack[-1]
            Xid = TreeNodes[-1]
            if X == a.name:
                Stack.pop()
                TreeNodes.pop()
                n = T.add_node(a.name, Xid)
                T.add_node(a, n)
                a = Lexer.get_next_token()
                if not a:
                    a = Token(END_OF_STRING, END_OF_STRING)
            elif X in self.grammar.sigma:
                raise ValueError("parse failed")
            elif self.M[X, a.name] is None:
                raise ValueError("parse failed")
            else:
                Stack.pop()
                TreeNodes.pop()
                for symbol in self.M[X, a.name]:
                    n = T.add_node(symbol, Xid)
                    if symbol != EPSI:
                        Stack.append(symbol)
                        TreeNodes.append(n)
        return T


class LR1(Parser):
    def __init__(self, grammar: CFG):
        super().__init__(grammar)
        self.ACTION: dict[[int, str], tuple[str, str, int]] = {}
        self.GOTO: dict[[int, str], int] = {}

    def add_ACTION(self, state_id : int, symbol : str, op_type : str, data1 : str, data2 : int):
        if not self.ACTION.get((state_id, symbol)):
            self.ACTION[state_id, symbol] = (op_type, data1, data2)
        else:
            raise ValueError("the grammar could not be processed by the parser")

    def add_GOTO(self, from_state_id : int, symbol : str, to_state_id):
        self.GOTO[from_state_id, symbol] = to_state_id

    def parse(self, code: str, Lexer: LexicalAnalyzer) -> ParseTree:
        T = ParseTree(self.grammar)
        Lexer.set_input(code)
        Stack = [0]
        Symbols: list[str] = []
        TreeRoots: list[int] = []
        a = Lexer.get_next_token()
        while True:
            s = Stack[-1]
            if self.ACTION[s, a.name][0] == "shift":
                Stack.append(self.ACTION[s, a.name][2])
                n = T.add_node(a)
                Symbols.append(a.name)
                TreeRoots.append(n)
                a = Lexer.get_next_token()
                if not a:
                    a = Token(END_OF_STRING, END_OF_STRING)
            elif self.ACTION[s, a.name][0] == "reduce":
                A = self.ACTION[s, a.name][1]
                β = self.grammar.productions[A][self.ACTION[s, a.name][2]]
                root = T.add_node(A)
                for i in range(0, len(β)):
                    Stack.pop()
                    head = Symbols.pop()
                    child = TreeRoots.pop()
                    T.children[root].append(child)
                t = Stack[-1]
                Stack.append(self.GOTO[t, A])
                Symbols.append(A)
                TreeRoots.append(root)
            elif self.ACTION[s, a.name][0] == "accept":
                T.set_root(TreeRoots[-1])
                return T
            else:
                raise ValueError("Syntax Error")


class Item:
    def __init__(self, head: str, production_id: int, dot_pos: int):
        self.head = head
        self.production_id = production_id
        self.dot_pos = dot_pos
    def __hash__(self):
        return hash({"head": self.head, "production_id": self.production_id, "dot_pos": self.dot_pos})
    def __eq__(self, other):
        return self.head == other.head and self.production_id == other.production_id and self.dot_pos == other.dot_pos


class SetOfItems:
    def __init__(self, grammar: CFG, items: set[Item]):
        self.grammar = grammar
        self.items = items

    def CLOSURE(self):
        J = self.items
        J_prev = self.items
        flag = True
        while flag:
            J_new = set()
            for item in J_prev:
                head, n, pos = item.head, item.production_id, item.dot_pos
                flag = False
                if (pos <= len(self.grammar.productions[head][n])
                        and self.grammar.productions[head][n][pos] not in self.grammar.sigma):
                    B = self.grammar.productions[head][n][pos]
                    for i, _ in enumerate(self.grammar.productions[B]):
                        if (head, i, 0) not in J:
                            flag = True
                            J_new.add(Item(B, i, 0))
            J = J.union(J_new)
            J_prev = J_new
        return SetOfItems(self.grammar, J)

    def GOTO(self, X: str):
        J = set()
        for item in self.items:
            head, n, pos = item.head, item.production_id, item.dot_pos
            if pos <= len(self.grammar.productions[head][n]) and self.grammar.productions[head][n][pos] == X:
                J.add(Item(head, n, pos + 1))
        return SetOfItems(self.grammar, J).CLOSURE()

    def __hash__(self):
        return hash(frozenset(self.items))
    def __eq__(self, other):
        return self.items == other.items


class SLR1(LR1):

    def __init__(self, grammar: CFG):
        super().__init__(grammar)
        self.set_parsing_table()
        self.grammar = CFG(
            [f"<__{self.grammar.start_symbol}'> ::= <{self.grammar.start_symbol}>"] + self.grammar.raw_productions)
        self.set_parsing_table()

    def set_parsing_table(self):
        C0 = SetOfItems(self.grammar, {Item(self.grammar.start_symbol, 0, 0)}).CLOSURE()
        C : set[SetOfItems] = {C0}
        C_prev : set[SetOfItems] = {C0}
        C_id : dict[SetOfItems, int] = {C0 : 0}
        id_next = 1
        flag = True
        while flag:
            C_new = set()
            flag = False
            for I in C_prev:
                for item in I.items:
                    head, n, pos = item.head, item.production_id, item.dot_pos
                    if head == self.grammar.start_symbol and pos == 1:
                        self.add_ACTION(C_id[I], head, "accept", "", 0)
                        continue
                    elif pos >= len(self.grammar.productions[head][n]):
                        for a in self.grammar.FOLLOW[head]:
                            self.add_ACTION(C_id[I], a, "reduce", head, n)
                        continue
                    X = self.grammar.productions[head][n][pos]
                    I_next = I.GOTO(X)
                    if I_next not in C:
                        flag = True
                        C_id[I_next] = id_next
                        id_next += 1
                        C_new.add(I_next)
                    self.add_GOTO(C_id[I], X, C_id[I_next])
                    self.add_ACTION(C_id[I], X, "shift", "", C_id[I_next])
            C = C.union(C_new)
            C_prev = C_new


class CLR1(LR1):
    pass


class LALR1(LR1):
    pass
