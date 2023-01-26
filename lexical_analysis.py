from typing import Callable
from enum import Enum


class RESERVED(Enum):
    LEFT_BRACKET = "("
    RIGHT_BRACKET = ")"
    STAR = "*"
    OR = "|"
    AND = "."


END_OF_STRING, EPSI, ESCAPE, LEFT_BRACKET, RIGHT_BRACKET, STAR, OR, AND = '#', 'ε', '%', RESERVED.LEFT_BRACKET, RESERVED.RIGHT_BRACKET, RESERVED.STAR, RESERVED.OR, RESERVED.AND
RESERVED_DICT = {i.value: i for i in RESERVED}


class DFA:
    def __init__(self, size: int, sigma: list[str]):
        self.size = size
        self.sigma = sigma
        self.next: list[dict[str, int]] = [dict(zip(sigma, [-1] * len(sigma))) for i in range(self.size)]
        self.accept: list[bool] = [False] * self.size
        self.now = 0

    def set_accept(self, node: int):
        self.accept[node] = True

    def set_transition(self, start: int, end: int, through: str):
        self.next[start][through] = end

    def setup_match(self):
        self.now = 0

    def getchar_match(self, c : str):
        self.now = self.next[self.now][c]
        if self.accept[self.now]:
            return True
        return False

    def match(self, target: str) -> bool:
        self.setup_match()
        for c in target[:-1]:
            self.getchar_match(c)
        return self.getchar_match(target[-1])

    def state_minimization(self):
        group = [1 if self.accept[i] else 0 for i in range(self.size)]
        F = list(filter(lambda x: self.accept[x], [i for i in range(self.size)]))
        F_prime = list(filter(lambda x: not self.accept[x], [i for i in range(self.size)]))
        P = [F, F_prime]
        P_new = []
        flag = True

        def update_group():
            for i, G in enumerate(P_new):
                for s in G:
                    group[s] = i

        while flag:
            flag = False
            for i in range(len(P)):
                G = [P.pop(0)]  # Use a deque here for better performance
                for c in self.sigma:
                    new_G = []
                    for G_i in G:
                        G_dict = {}
                        for j in range(self.size):
                            G_dict[group[j]] = []
                        for s in G_i:
                            G_dict[group[self.next[s][c]]].append(s)
                        if list(G_dict.values()).count([]) != len(G_dict.values()) - 1:
                            flag = True
                        for new_G_i in G_dict.values():
                            if new_G_i:
                                new_G.append(new_G_i)
                    G = new_G
                P_new += G
            update_group()
            P = P_new

        D = DFA(len(P), self.sigma)
        P[group[0]], P[0] = P[0], P[group[0]]
        update_group()
        for G in P:
            for c in self.sigma:
                D.set_transition(group[G[0]], group[self.next[G[0]][c]], c)
            for s in G:
                if self.accept[s]:
                    D.set_accept(group[s])
        return D


class NFA:
    def __init__(self, size: int, sigma: list[str]):
        self.size = size
        self.sigma = sigma
        self.next: list[dict[str, list[int]]] = [dict(zip(sigma + [EPSI], [list() for j in range(len(sigma) + 1)])) for
                                                 i in range(self.size)]
        self.accept: list[bool] = [False] * self.size
        self.T : list[int] = []
        self.A : list[int] = []

    def set_accept(self, node: int):
        self.accept[node] = True

    def set_transition(self, start: int, end: int, through: str):
        self.next[start][through].append(end)

    def epsi_closure(self, T: list[int]) -> list[int]:
        visited = [False] * self.size
        for node in T:
            visited[node] = True
        flag = True
        while flag:
            flag = False
            for i in range(0, self.size):
                if visited[i]:
                    for node in self.next[i][EPSI]:
                        if not visited[node]:
                            flag = True
                            visited[node] = True
        T_prime = []
        for i in range(0, self.size):
            if visited[i]:
                T_prime.append(i)
        return T_prime

    def move(self, T: list[int], a: str) -> list[int]:
        visited = [False] * self.size
        for start in T:
            for end in self.next[start][a]:
                visited[end] = True
        T_prime = []
        for i in range(0, self.size):
            if visited[i]:
                T_prime.append(i)
        return T_prime

    def setup_match(self):
        self.T = self.epsi_closure([0])
        self.A = []
        for i in range(0, self.size):
            if self.accept[i]:
                self.A.append(i)

    def getchar_match(self, c : str):
        self.T = self.epsi_closure(self.move(self.T, c))
        if set(self.T).intersection(set(self.A)) != set():
            return True
        return False

    def match(self, target: str) -> bool:
        self.setup_match()
        for c in target[:-1]:
            self.getchar_match(c)
        return self.getchar_match(target[-1])

    # Using counting sort instead of the built-in sorted function provides better performance
    def subset_construction(self) -> DFA:
        T0 = tuple(sorted(self.epsi_closure([0])))
        Dstates: set = {T0}
        unvisited: set = {T0}
        DTran: list[dict[str, int]] = [{}]
        StatesId = {T0: 0}
        DSize = 1
        sigma_prime = list(set(self.sigma).difference(set(EPSI)))
        while unvisited != set():
            T = unvisited.pop()
            for a in sigma_prime:
                U = tuple(sorted(self.epsi_closure(self.move(T, a))))
                if U not in Dstates:
                    Dstates.add(U)
                    unvisited.add(U)
                    StatesId[U] = DSize
                    DTran.append(dict(zip(sigma_prime, [-1] * len(sigma_prime))))
                    DSize += 1
                DTran[StatesId[T]][a] = StatesId[U]
        D = DFA(DSize, sigma_prime)
        D.next = DTran
        for Dstate in list(Dstates):
            for NState in Dstate:
                if self.accept[NState]:
                    D.set_accept(StatesId[Dstate])
        return D


class Regex:
    # the Kleene stars in my system are right-associative instead of left
    def __init__(self, raw: str):
        self.sigma = set()
        S = list("(" + raw.replace(" ", "") + ")" + END_OF_STRING)
        self.S = []
        self.sigma = list(filter(lambda x: x not in RESERVED_DICT and x not in [EPSI, ESCAPE], S))
        # Use a stack here for better performance
        while S:
            c = S.pop(0)
            if c == ESCAPE:
                c = S.pop(0)
                self.S.append(c)
            elif c == "*" and S[0] != "(":
                self.S.extend([STAR, RESERVED.LEFT_BRACKET, S.pop(0), RESERVED.RIGHT_BRACKET])
            elif c not in RESERVED_DICT or c == EPSI:
                self.S.append(c)
            else:
                self.S.append(RESERVED_DICT[c])
        self.N = NFA(len(self.S) * 4, self.sigma)
        self.value: list[str | RESERVED] = [""] * (len(self.S) * 4)
        self.left_child: list[None | int] = [None] * (len(self.S) * 4)
        self.right_child: list[None | int] = [None] * (len(self.S) * 4)
        self.nullable = [False for i in range(len(self.S) * 4)]
        self.firstpos = [set() for i in range(len(self.S) * 4)]
        self.lastpos = [set() for i in range(len(self.S) * 4)]
        self.followpos = [set() for i in range(len(self.S) * 4)]
        self.next_node = 1
        self.next_state = 1
        self.next_token = 0
        self.parse(0, AND)
        if self.next_token < len(self.S):
            raise ValueError("Invalid Regex Syntax")

    def parse(self, father: int, mode: RESERVED):
        now_token = self.next_token
        now_node = self.next_node
        self.next_node += 1
        left_child = self.next_node
        self.next_node += 1
        if mode == OR:
            if self.S[now_token] not in list(RESERVED) or self.S[now_token] == STAR or self.S[now_token] == LEFT_BRACKET:
                self.parse(now_node, AND)
            else:
                raise ValueError("Invalid Regex Syntax")
        elif mode == AND:
            if now_token >= len(self.S) or self.S[now_token] == RIGHT_BRACKET or self.S[now_token] == OR:
                return
            elif self.S[now_token] not in list(RESERVED):
                self.next_token += 1
                self.left_child[now_node] = left_child
                self.value[left_child] = self.S[now_token]
                self.parse(now_node, AND)
            elif self.S[now_token] == STAR:
                self.next_token += 2
                self.left_child[now_node] = left_child
                self.value[left_child] = self.S[now_token]
                self.parse(left_child, OR)
            elif self.S[now_token] == LEFT_BRACKET:
                self.next_token += 1
                self.parse(now_node, OR)

        now_token = self.next_token
        if mode == OR:
            if now_token >= len(self.S) or self.S[now_token] == RIGHT_BRACKET:
                self.next_token += 1
            elif self.S[now_token] == OR:
                self.next_token += 1
                self.parse(now_node, OR)
            else:
                raise ValueError("Invalid Regex Syntax")
        elif mode == AND:
            if now_token >= len(self.S) or self.S[now_token] == RIGHT_BRACKET or self.S[now_token] == OR:
                pass
            elif self.S[now_token] not in list(RESERVED) or self.S[now_token] == STAR or self.S[
                now_token] == LEFT_BRACKET:
                self.parse(now_node, AND)

        if self.left_child[now_node] is not None and self.right_child[now_node] is not None:
            self.value[now_node] = mode

        left_child = self.left_child[now_node]
        if self.value[now_node] == "":
            if self.left_child[father] is None:
                self.left_child[father] = left_child
            else:
                self.right_child[father] = left_child
        else:
            if self.left_child[father] is None:
                self.left_child[father] = now_node
            else:
                self.right_child[father] = now_node

    # Any strings feeding into a NFA generated by this method must add the # delimiter to obtain the correct result
    def to_NFA(self) -> NFA:
        (start, end) = self.to_NFA_(self.left_child[0])
        self.N.set_transition(0, start, EPSI)
        self.N.set_accept(end)
        return self.N

    def to_NFA_(self, now) -> (int, int):
        now_v = self.value[now]
        if now_v not in list(RESERVED):
            s1 = self.next_state
            s2 = self.next_state + 1
            self.next_state += 2
            self.N.set_transition(s1, s2, now_v)
            return s1, s2
        elif now_v == AND:
            (start1, end1) = self.to_NFA_(self.left_child[now])
            (start2, end2) = self.to_NFA_(self.right_child[now])
            self.N.set_transition(end1, start2, EPSI)
            return start1, end2
        elif now_v == STAR:
            (start, end) = self.to_NFA_(self.left_child[now])
            s1 = self.next_state
            s2 = self.next_state + 1
            self.next_state += 2
            self.N.set_transition(s1, start, EPSI)
            self.N.set_transition(s1, s2, EPSI)
            self.N.set_transition(end, start, EPSI)
            self.N.set_transition(end, s2, EPSI)
            return s1, s2
        elif now_v == OR:
            (start1, end1) = self.to_NFA_(self.left_child[now])
            (start2, end2) = self.to_NFA_(self.right_child[now])
            s1 = self.next_state
            s2 = self.next_state + 1
            self.next_state += 2
            self.N.set_transition(s1, start1, EPSI)
            self.N.set_transition(s1, start2, EPSI)
            self.N.set_transition(end1, s2, EPSI)
            self.N.set_transition(end2, s2, EPSI)
            return s1, s2

    # Any strings feeding into a DFA generated by this method must add the # delimiter to obtain the correct result
    def to_DFA(self) -> DFA:
        self.get_summaries(self.left_child[0])
        T0 = tuple(sorted(self.firstpos[self.left_child[0]]))
        DStates = {T0}
        unvisited = {T0}
        DTran: list[dict[str, int]] = [{}]
        StatesId = {T0: 0}
        DSize = 1
        end_of_exp = self.right_child[self.left_child[0]]
        sigma_prime = list(set(self.sigma).difference(set(EPSI)))
        while unvisited != set():
            S = unvisited.pop()
            for a in sigma_prime:
                U = set()
                for s in S:
                    if self.value[s] == a:
                        U = U.union(self.followpos[s])
                U_key = tuple(sorted(U))
                if U_key not in DStates:
                    StatesId[U_key] = DSize
                    DSize += 1
                    DStates.add(U_key)
                    DTran.append(dict(zip(sigma_prime, [-1] * len(sigma_prime))))
                    unvisited.add(U_key)
                DTran[StatesId[S]][a] = StatesId[U_key]
        D = DFA(DSize, sigma_prime)
        D.next = DTran
        for S in DStates:
            if end_of_exp in S:
                D.set_transition(StatesId[S], StatesId[S], '#')
                D.set_accept(StatesId[S])
        return D

    def get_summaries(self, now):
        if self.value[now] == EPSI:
            self.nullable[now] = True
            self.firstpos[now] = {}
            self.lastpos[now] = {}
        elif self.value[now] not in list(RESERVED):
            self.nullable[now] = False
            self.firstpos[now] = {now}
            self.lastpos[now] = {now}
        elif self.value[now] == OR:
            self.get_summaries(self.left_child[now])
            self.get_summaries(self.right_child[now])
            self.nullable[now] = self.nullable[self.left_child[now]] or self.nullable[self.right_child[now]]
            self.firstpos[now] = self.firstpos[self.left_child[now]].union(self.firstpos[self.right_child[now]])
            self.lastpos[now] = self.lastpos[self.left_child[now]].union(self.lastpos[self.right_child[now]])
        elif self.value[now] == AND:
            self.get_summaries(self.left_child[now])
            self.get_summaries(self.right_child[now])
            self.nullable[now] = self.nullable[self.left_child[now]] and self.nullable[self.right_child[now]]
            if self.nullable[self.left_child[now]]:
                self.firstpos[now] = self.firstpos[self.left_child[now]].union(self.firstpos[self.right_child[now]])
            else:
                self.firstpos[now] = self.firstpos[self.left_child[now]]
            if self.nullable[self.right_child[now]]:
                self.lastpos[now] = self.lastpos[self.left_child[now]].union(self.lastpos[self.right_child[now]])
            else:
                self.lastpos[now] = self.lastpos[self.right_child[now]]
            for i in self.lastpos[self.left_child[now]]:
                self.followpos[i] = self.followpos[i].union(self.firstpos[self.right_child[now]])
        elif self.value[now] == STAR:
            self.get_summaries(self.left_child[now])
            self.nullable[now] = True
            self.firstpos[now] = self.firstpos[self.left_child[now]]
            self.lastpos[now] = self.lastpos[self.left_child[now]]
            for i in self.lastpos[self.left_child[now]]:
                self.followpos[i] = self.followpos[i].union(self.firstpos[self.left_child[now]])


class Token:
    def __init__(self, name: str, lexeme : str):
        self.name = name
        self.attributes = {"lexeme" : lexeme}


class LexicalAnalyzer:
    def __init__(self, patterns: list[str, str], mode: str, preprocessor: Callable[[str], str] = lambda x: x):
        self.engines: dict[str: DFA | NFA] = {}
        for name, expression in patterns:
            if mode == 'NFA':
                self.engines[name] = Regex(expression).to_NFA()
            else:
                self.engines[name] = Regex(expression).to_DFA()
            self.engines[name].setup_match()
        self.input = ""
        self.token_list: list[Token] = []
        self.lexeme_begin = 0
        self.forward = 0
        self.preprocessor = preprocessor

    def set_input(self, input_str):
        self.input = self.preprocessor(input_str) + END_OF_STRING
        self.token_list = []
        self.lexeme_begin = 0
        self.forward = 0

    def get_next_token(self) -> Token | bool:
        if self.forward >= len(self.input):
            return False
        matched = []
        previously_matched = []
        lexeme = ""
        while self.forward < len(self.input) and self.input[self.forward] != END_OF_STRING:
            c = self.input[self.forward]
            lexeme += c
            self.forward += 1
            for name, E in zip(self.engines.keys(), self.engines.values()):
                E.getchar_match(c)
                E_T = E.T
                if E.getchar_match(END_OF_STRING):
                    E.T = E_T
                    matched.append(name)
            if not matched and previously_matched:
                new_token = Token(previously_matched[0], lexeme[:-1])
                self.token_list.append(new_token)
                self.forward -= 1
                self.lexeme_begin = self.forward
                for E in self.engines.values():
                    E.setup_match()
                return new_token
            previously_matched = matched
        raise ValueError("Lexical Error")


if __name__ == '__main__':
    D = DFA(4, ['a', 'b'])
    D.set_accept(3)
    D.set_transition(0, 0, 'b')
    D.set_transition(0, 1, 'a')
    D.set_transition(1, 1, 'a')
    D.set_transition(1, 2, 'b')
    D.set_transition(2, 1, 'a')
    D.set_transition(2, 3, 'b')
    D.set_transition(3, 1, 'a')
    D.set_transition(3, 0, 'b')
    print(D.match("abababababb"))
    print(D.match("abba"), "\n")

    N = NFA(11, ['a', 'b'])
    N.set_accept(10)
    N.set_transition(0, 1, EPSI)
    N.set_transition(0, 7, EPSI)
    N.set_transition(1, 2, EPSI)
    N.set_transition(1, 4, EPSI)
    N.set_transition(2, 3, 'a')
    N.set_transition(4, 5, 'b')
    N.set_transition(3, 6, EPSI)
    N.set_transition(5, 6, EPSI)
    N.set_transition(6, 1, EPSI)
    N.set_transition(6, 7, EPSI)
    N.set_transition(7, 8, 'a')
    N.set_transition(8, 9, 'b')
    N.set_transition(9, 10, 'b')
    print(N.match("abababababb"))
    print(N.match("abba"), "\n")

    D_new = N.subset_construction()
    print(D_new.match("abababababb"))
    print(D_new.match("abba"))
    D_new_minimized = D_new.state_minimization()
    print(D_new_minimized.size)
    print(D_new_minimized.match("abababababb"))
    print(D_new_minimized.match("abba"), "\n")

    R = Regex("*(a | b)abb")
    print(R.to_NFA().match("abababababb#"))
    print(R.to_NFA().match("abba#"))
    print(R.to_DFA().match("abababababb#"))
    print(R.to_DFA().match("abba#"))
