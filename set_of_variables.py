
class Formula(object):  #data structure
    pass


class Const(Formula):
    def __init__(self, value):
        self.value = value

    @staticmethod
    def get_variables():
        return set()

    def evaluate(self, assignment):
        return self.value

    def __str__(self):
        return str(self.value)


class Var(Formula):
    def __init__(self, name):
        self.name = name

    def get_variables(self):
        return {self.name}

    def evaluate(self, assignment):
        return assignment[self.name]

    def __str__(self):
        return self.name


class Add(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def get_variables(self):
        return self.left.get_variables() | self.right.get_variables()

    def evaluate(self, assignment):
        return self.left.evaluate(assignment) + self.right.evaluate(assignment)

    def __str__(self):
        return "({} + {})".format(self.left, self.right)


class Mul(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def get_variables(self):
        return self.left.get_variables() | self.right.get_variables()

    def evaluate(self, assignment):
        return self.left.evaluate(assignment) * self.right.evaluate(assignment)

    def __str__(self):
        return "({} * {})".format(self.left, self.right)


formula = Add(Mul(Add(Var("y"), Var("x")), Var("y")), Const(0))

print(formula.evaluate({"x": 1, "y": 2}))

print(formula.get_variables())

print(formula)
