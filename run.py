
from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood

import random

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

teams = {    #Dictionary to store teams, players, and their cards
    "teamX": {
        "player1": {
            "card1": {"type": "", "value": ""},
            "card2": {"type": "", "value": ""}
        },
        "player3": {
            "card1": {"type": "", "value": ""},
            "card2": {"type": "", "value": ""}
        }
    },
    "teamY": {
        "player2": {
            "card1": {"type": "", "value": ""},
            "card2": {"type": "", "value": ""}
        },
        "player4": {
            "card1": {"type": "", "value": ""},
            "card2": {"type": "", "value": ""}
        }
    }
}    #Example acess: teams["teamX"]["player1"]["card1"]["type"]

deck = {
    "hearts": [1, 2, 3, 4, 5, 6],
    "diamonds": [1, 2, 3, 4, 5, 6],
    "spades": [1, 2, 3, 4, 5, 6],
    "clubs": [1, 2, 3, 4, 5, 6]
}

suitMap = {1: "hearts", 2: "diamonds", 3: "spades", 4: "clubs"}

def deal(deck):
    while True:
        s = random.randint(1, 4)  #Randomly pick a suit
        suit = suitMap[s]    #Map random number to suit
        v = random.randint(1, 6)  #Randomly pick a value

        if v in deck[suit]:      #Check card is still in deck 
            deck[suit].remove(v)     #Update deck
            return suit, v  
    

#Assign player cards
cardMap = [
    ("teamX", "player1", "card1"),
    ("teamX", "player1", "card2"),
    ("teamY", "player2", "card1"),
    ("teamY", "player2", "card2"),
    ("teamX", "player3", "card1"),
    ("teamX", "player3", "card2"),
    ("teamY", "player4", "card1"),
    ("teamY", "player4", "card2")
]

# Assign cards to each player
for team, player, card in cardMap:
    suit, value = deal(deck)
    teams[team][player][card]["type"] = suit
    teams[team][player][card]["value"] = value


tricks = {"t1": False, "t2": False, "t3": False, "t4": False, "t5": False, }  #Initialize each trick to false




# Encoding that will store all of your constraints
E = Encoding()

# To create propositions, create classes for them first, annotated with "@proposition" and the Encoding
@proposition(E)
class BasicPropositions:

    def __init__(self, data):
        self.data = data

    def _prop_name(self):
        return f"A.{self.data}"


# Different classes for propositions are useful because this allows for more dynamic constraint creation
# for propositions within that class. For example, you can enforce that "at least one" of the propositions
# that are instances of this class must be true by using a @constraint decorator.
# other options include: at most one, exactly one, at most k, and implies all.
# For a complete module reference, see https://bauhaus.readthedocs.io/en/latest/bauhaus.html
@constraint.at_least_one(E)
@proposition(E)
class FancyPropositions:

    def __init__(self, data):
        self.data = data

    def _prop_name(self):
        return f"A.{self.data}"

# Call your variables whatever you want
a = BasicPropositions("a")
b = BasicPropositions("b")   
c = BasicPropositions("c")
d = BasicPropositions("d")
e = BasicPropositions("e")
# At least one of these will be true
x = FancyPropositions("x")
y = FancyPropositions("y")
z = FancyPropositions("z")


# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def example_theory():
    # Add custom constraints by creating formulas with the variables you created. 
    E.add_constraint((a | b) & ~x)
    # Implication
    E.add_constraint(y >> z)
    # Negate a formula
    E.add_constraint(~(x & y))
    # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    constraint.add_exactly_one(E, a, b, c)

    return E


if __name__ == "__main__":

    T = example_theory()
    # Don't compile until you're finished adding all your constraints!
    T = T.compile()
    # After compilation (and only after), you can check some of the properties
    # of your model:
    print("\nSatisfiable: %s" % T.satisfiable())
    print("# Solutions: %d" % count_solutions(T))
    print("   Solution: %s" % T.solve())

    print("\nVariable likelihoods:")
    for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
        # Ensure that you only send these functions NNF formulas
        # Literals are compiled to NNF here
        print(" %s: %.2f" % (vn, likelihood(T, v)))
    print()
