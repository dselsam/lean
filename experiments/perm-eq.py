from random import shuffle
import sys

def printHeader(numElems):
    print """import data.list.perm
open list perm option nat

definition denote [reducible] {X : Type} (default : X) [add_comm_semigroup X] (xs : list X) : list nat -> X
| nil := default
| (cons i is) := match nth xs i with
                 | none := default
                 | (some x) := match is with
                               | nil := x
                               | _ := x + denote is
                               end
                 end

axiom perm_ac {X : Type} (default : X) [add_comm_semigroup X] (xs : list X) (is js : list nat) : 
  perm is js -> denote default xs is = denote default xs js
constants (X : Type.{1}) (X_acsg : add_comm_semigroup X) (X_deceq : decidable_eq X)
attribute X_acsg [instance]
attribute X_deceq [instance]
"""
    sys.stdout.write("constants (")
    for i in range(numElems):
        sys.stdout.write("x{} ".format(i))
    print " : X)"

def writeAdd(xs):
    first = True
    for x in xs:
        if first: sys.stdout.write("x{}".format(x))
        else: sys.stdout.write(" + (x{}".format(x))
        first = False
    for x in range(len(xs)-1):
        sys.stdout.write(")")

def writeList(xs):
    sys.stdout.write("[")
    first = True
    for x in xs:
        if first: sys.stdout.write("{}".format(x))
        else: sys.stdout.write(", {}".format(x))
        first = False
    sys.stdout.write("] ")
        
def printExample(numElems):
    print "---------"
    xs = [i for i in range(numElems)]
    shuffle(xs)
    ys = [i for i in range(numElems)]
    shuffle(ys)
    sys.stdout.write("example : ")
    writeAdd(xs)
    sys.stdout.write(" = ")    
    writeAdd(ys)
    sys.stdout.write(" := perm_ac x0 ")
    writeList(["x{}".format(i) for i in range(numElems)])
    writeList(xs)
    writeList(ys)
    print "dec_trivial"

numElems = 20
numExamples = 100

printHeader(numElems)

for i in range(numExamples):
    printExample(numElems)
