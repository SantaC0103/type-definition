
class Set:
    pass


class Empty(Set):

    @staticmethod
    def results():
        return set()


class Var(Set):
    def __init__(self, name):
        self.name = name

    def results(self):
        return {self.name}


class Lit(Set):
    def __init__(self, value):
        self.value = value

    def results(self):
        return self.value


class Uni(Set):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def results(self):
        return self.left.results() | self.right.results()


class Int(Set):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def results(self):
        return self.left.results() & self.right.results()


class Dif(Set):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def results(self):
        return self.left.results() - self.right.results()




def update1(set): # update rules for live variable analysis
    oset = set
    set[0] = set[5]
    set[1] = Uni(set[6],set[7])
    set[2] = set[5]
    set[3] = Empty()
    set[4] = Dif(oset[0],Lit({"x"}))
    set[5] = Uni(oset[1],Lit({"y"}))
    set[6] = Uni(oset[2],Lit({"x"}))
    set[7] = Dif(oset[3],Lit({"x"}))
    return set


def update2(set): # update rules for available expression analysis
    oset = set
    print(oset)
    set[0] = Empty()
    set[1] = oset[5]
    set[2] = Int(oset[6], oset[9])
    set[3] = oset[7]
    set[4] = oset[8]
    set[5] = Uni(oset[0],Lit({"a+b"}))
    set[6] = Uni(oset[1],Lit({"a*b"}))
    set[7] = Uni(oset[2],Lit({"a+b"}))
    set[8] = Dif(oset[3],Lit({"a+b","a*b","a+1"}))
    set[9] = Uni(oset[4],Lit({"a+b"}))
    return set


def eq(a,b,n):  # estimate if two list of set are equal
    for i in range(n):
        if a[i] != b[i].results:
            return False
    return True


def Ffp(set,type):  # do the update, type 1 is live variable analysis and type2 is available expression analysis
    flag = 1
    while(flag):
        oset = []
        for i in range(len(set)):
            oset.append(set[i].results())
        if type == 1:
            set = update1(set)
        else: set = update2(set)
        if eq(oset, set, len(set)):
            for i in range(len(set)):
                print(set[i].results())
            break


def main():  #beginning of the assignment
    set1 = [Empty(), Empty(), Empty(), Empty(), Empty(), Empty(), Empty(), Empty()]
    set2 = [Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"}), Lit({"a+b","a*b","a+1"})]
    Ffp(set1,1)
    Ffp(set2, 2)

main()
