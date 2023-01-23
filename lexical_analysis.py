EPSI = 'ε'
RESERVED = ["(", ")", "*", "|", ".", EPSI]


class DFA:
    def __init__(self, size: int, sigma: list[str]):
        self.size = size
        self.sigma = sigma
        self.next: list[dict[str, int]] = [dict(zip(sigma, [-1] * len(sigma))) for i in range(self.size)]
        self.accept: list[bool] = [False] * self.size

    def set_accept(self, node: int):
        self.accept[node] = True

    def set_transition(self, start: int, end: int, through: str):
        self.next[start][through] = end

    def match(self, target: str) -> bool:
        now = 0
        if self.accept[now]:
            return True
        for c in target:
            now = self.next[now][c]
            if now == -1:
                return False
        if self.accept[now]:
            return True
        return False

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
                G = [P.pop(0)] #Use a deque here for better performance
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

    def match(self, target: str) -> bool:
        T = self.epsi_closure([0])
        A = []
        for i in range(0, self.size):
            if self.accept[i]:
                A.append(i)
        if set(T).intersection(set(A)) != set():
            return True
        for c in target:
            T = self.epsi_closure(self.move(T, c))
        if set(T).intersection(set(A)) != set():
            return True
        return False

    # Using counting sort instead of the built-in sorted function provides better performance
    def subset_construction(self) -> DFA:
        T0 = tuple(sorted(self.epsi_closure([0])))
        Dstates: set = {T0}
        unvisited: set = {T0}
        DTran: list[dict[str, int]] = [{}]
        StatesId = {T0: 0}
        DSize = 1
        while unvisited != set():
            T = unvisited.pop()
            for a in self.sigma:
                U = tuple(sorted(self.epsi_closure(self.move(T, a))))
                if U not in Dstates:
                    Dstates.add(U)
                    unvisited.add(U)
                    StatesId[U] = DSize
                    DTran.append(dict(zip(self.sigma, [-1] * len(self.sigma))))
                    DSize += 1
                DTran[StatesId[T]][a] = StatesId[U]
        D = DFA(DSize, self.sigma)
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
        S = list("(" + raw.replace(" ", "") + ")#")
        self.S = []
        # Use a stack here for better performance
        while S:
            c = S.pop(0)
            if c not in RESERVED:
                self.sigma.add(c)
            self.S.append(c)
            if c == "*" and S[0] != "(":
                self.S.extend(["(", S.pop(0), ")"])
        self.sigma = list(self.sigma)
        self.N = NFA(len(self.S) * 4, self.sigma)
        self.value: list[str] = [""] * (len(self.S) * 4)
        self.left_child: list[None | int] = [None] * (len(self.S) * 4)
        self.right_child: list[None | int] = [None] * (len(self.S) * 4)
        self.nullable = [False for i in range(len(self.S) * 4)]
        self.firstpos = [set() for i in range(len(self.S) * 4)]
        self.lastpos = [set() for i in range(len(self.S) * 4)]
        self.followpos = [set() for i in range(len(self.S) * 4)]
        self.next_node = 1
        self.next_state = 1
        self.next_token = 0
        self.parse(0, ".")

    def parse(self, father: int, mode: str):
        now_token = self.next_token
        now_node = self.next_node
        self.next_node += 1
        left_child = self.next_node
        self.next_node += 1
        if mode == '|':
            if self.S[now_token] not in RESERVED[:5] or self.S[now_token] == '*' or self.S[now_token] == '(':
                self.parse(now_node, ".")
            else:
                raise ValueError("Invalid Regex Syntax")
        elif mode == '.':
            if now_token >= len(self.S) or self.S[now_token] == ')' or self.S[now_token] == '|':
                return
            elif self.S[now_token] not in RESERVED[:5]:
                self.next_token += 1
                self.left_child[now_node] = left_child
                self.value[left_child] = self.S[now_token]
                self.parse(now_node, ".")
            elif self.S[now_token] == '*':
                self.next_token += 2
                self.left_child[now_node] = left_child
                self.value[left_child] = '*'
                self.parse(left_child, "|")
            elif self.S[now_token] == '(':
                self.next_token += 1
                self.parse(now_node, "|")

        now_token = self.next_token
        if mode == '|':
            if now_token >= len(self.S) or self.S[now_token] == ')':
                self.next_token += 1
            elif self.S[now_token] == '|':
                self.next_token += 1
                self.parse(now_node, '|')
            else:
                raise ValueError("Invalid Regex Syntax")
        elif mode == '.':
            if now_token >= len(self.S) or self.S[now_token] == ')' or self.S[now_token] == '|':
                pass
            elif self.S[now_token] not in RESERVED[:5] or self.S[now_token] == '*' or self.S[now_token] == '(':
                self.parse(now_node, '.')

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
        if now_v not in RESERVED[:5]:
            s1 = self.next_state
            s2 = self.next_state + 1
            self.next_state += 2
            self.N.set_transition(s1, s2, now_v)
            return s1, s2
        elif now_v == '.':
            (start1, end1) = self.to_NFA_(self.left_child[now])
            (start2, end2) = self.to_NFA_(self.right_child[now])
            self.N.set_transition(end1, start2, EPSI)
            return start1, end2
        elif now_v == '*':
            (start, end) = self.to_NFA_(self.left_child[now])
            s1 = self.next_state
            s2 = self.next_state + 1
            self.next_state += 2
            self.N.set_transition(s1, start, EPSI)
            self.N.set_transition(s1, s2, EPSI)
            self.N.set_transition(end, start, EPSI)
            self.N.set_transition(end, s2, EPSI)
            return s1, s2
        elif now_v == '|':
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
                        U.union(self.followpos[s])
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
                D.set_accept(StatesId[S])
        return D

    def get_summaries(self, now):
        if self.value[now] == EPSI:
            self.nullable[now] = True
            self.firstpos[now] = {}
            self.lastpos[now] = {}
        elif self.value[now] not in RESERVED:
            self.nullable[now] = False
            self.firstpos[now] = {now}
            self.lastpos[now] = {now}
        elif self.value[now] == '|':
            self.get_summaries(self.left_child[now])
            self.get_summaries(self.right_child[now])
            self.nullable[now] = self.nullable[self.left_child[now]] or self.nullable[self.right_child[now]]
            self.firstpos[now] = self.firstpos[self.left_child[now]].union(self.firstpos[self.right_child[now]])
            self.lastpos[now] = self.lastpos[self.left_child[now]].union(self.lastpos[self.right_child[now]])
        elif self.value[now] == '.':
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
        elif self.value[now] == '*':
            self.get_summaries(self.left_child[now])
            self.nullable[now] = True
            self.firstpos[now] = self.firstpos[self.left_child[now]]
            self.lastpos[now] = self.lastpos[self.left_child[now]]
            for i in self.lastpos[self.left_child[now]]:
                self.followpos[i] = self.followpos[i].union(self.firstpos[self.left_child[now]])

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
    print(R.to_DFA().match("abba#"), "\n")