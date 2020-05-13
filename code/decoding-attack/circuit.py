import copy

class Wire(object):

    def __init__(self, id):
        self.variables = []
        if id is not None:
            self.variables.append(id)

    def xor(self, other):
        res = copy.deepcopy(self)
        for x in other.variables:
            if x in res.variables:
                res.variables.remove(x)
            else:
                res.variables.append(x)
        return res

class CircuitBuilder(object):

    def __init__(self):
        self.currentId = 0
        self.ONE = Wire(-1)
        self.ZERO = Wire(None)
        self.andGates = []
        self.outputWires = []

    def _getNewWire(self):
        w =  Wire(self.currentId)
        self.currentId += 1
        return w

    def addInputWire(self):
        return self._getNewWire()

    def XOR(self, a, b):
        return a.xor(b)

    def AND(self, a, b):
        w = self._getNewWire()
        self.andGates.append((a, b, w))
        return w

    def addOutputWire(self, w, value):
        self.outputWires.append((w, value))