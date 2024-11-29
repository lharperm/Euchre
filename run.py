
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
        suit = suitMap[random.randint(1, 4)]    #Map random number to suit
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

leftBower = {   #Define left bower 
        "hearts": "diamonds",
        "diamonds": "hearts",
        "spades": "clubs",
        "clubs": "spades"
}

def trump():
    t = suitMap[random.randint(1, 4)] #Define trump suit
    lb = leftBower[t] #Define bower

    for team in teams: #Update card type to trump if players card is trump
        for player in teams[team]:
            for card in teams[team][player]:
                type = teams[team][player][card]["type"]
                v = teams[team][player][card]["value"]

                if type == t:   #if type matches trump
                    teams[team][player][card]["type"] = "trump"
                
                if  (type == lb and v == 3):   #if card is left bower update its value and type
                    teams[team][player][card]["type"] = "trump"
                    teams[team][player][card]["value"] = 7

trumpRank = [1, 2, 4, 5, 6, 7, 3]   #Define trump hiearchy, 7 is left bower

# Encoding that stores constraints
E = Encoding()

@proposition(E)
class BasicPropositions:

    def __init__(self, data):
        self.data = data

    def _prop_name(self):
        return f"A.{self.data}"
    

#Define Variables
C1_vprime = BasicPropositions("C1_vprime")  
C2_vprime = BasicPropositions("C2_vprime")  


    # Define propositions for players holding the winning card
P1_c = BasicPropositions("P1_c")
P2_c = BasicPropositions("P2_c")
P3_c = BasicPropositions("P3_c")
P4_c = BasicPropositions("P4_c")

# Define propositions for teams winning the trick
T_TeamX = BasicPropositions("T_TeamX")
T_TeamY = BasicPropositions("T_TeamY")

T1 = BasicPropositions("T1")
T2 = BasicPropositions("T2")
T3 = BasicPropositions("T3")
T4 = BasicPropositions("T4")
T5 = BasicPropositions("T5")

@proposition(E)
class CalledTrump:
    def __init__(self):
        self.Q = BasicPropositions("Q")
        self.i = random.randint(0, 1)
        
        # Set Q based on random value
        if self.i == 1:
            self.Q = True
        else:
            self.Q = False

@proposition(E)           
class Tricks:
    def __init__(self):
        self.T = BasicPropositions("T")  
        self.tricks = []

        j = 1
        while j <= 3:  # Define winning team for tricks 1-3, True = X, False = Y
            self.i = random.randint(0, 1)  # Generate random result
            if self.i == 1:
                self.tricks.append(True)
            else:
                self.tricks.append(False)
            j += 1



@proposition(E)
class Win:
    def __init__(self, tricks_instance):

        #Define propositions for winning conditions (winning 3, 4, or 5 tricks)
        self.W3 = BasicPropositions("W3")
        self.W4 = BasicPropositions("W4")
        self.W5 = BasicPropositions("W5")

        #Count the number of tricks won by team X using the tricks dictionary from the Tricks instance
        for val in tricks_instance:
            if val == True:
                x_wins += 1

        self.W3 = (x_wins >= 3)
        self.W4 = (x_wins >= 4)
        self.W5 = (x_wins == 5)


        #Define Win_Wt as the logical OR of W3, W4, and W5
        self.Win_Wt = self.W3 | self.W4 | self.W5



@proposition(E)
class Euchre:
    def __init__(self, win_instance, trump_instance):
        
        self.W = win_instance.win_Wt
        self.C = trump_instance.Q

        #Define Euchre condition: E is True if W is false and C is true
        self.E = self.C & ~self.W

@proposition(E)
class IsTrump:
    def __init__(self, suit, trump_suit):
        self.suit = suit  # suit of the card being checked
        self.trump_suit = trump_suit  # current trump suit

    def is_trump(self):
        return self.suit == self.trump_suit  # true if the current card is of trump suit

@proposition(E)
class IsSuit:
    def __init__(self, team, player, card, lead_suit):
        self.card_suit = teams[team][player][card]["type"]  # Get the suit from the teams dictionary
        self.lead_suit = lead_suit  # Lead suit for the current trick

    def is_on_suit(self):
        # Return True only if the current card's suit matches the lead suit
        return self.card_suit == self.lead_suit

@proposition(E)
class PlayerHasWinningCard:
    def __init__(self, team, player, card, winning_card):
        # Check if the player is on Team X and holds the winning card
        self.is_team_x = team == "teamX"
        self.card_type = teams[team][player][card]["type"]
        self.card_value = teams[team][player][card]["value"]
        self.winning_card = winning_card  # Tuple (type, value) of winning card

    def has_winning_card(self):
        # Return True if the player is on Team X and holds the winning card
        return self.is_team_x and (self.card_type, self.card_value) == self.winning_card


@proposition(E)
class Lead:
    def __init__(self, tricks_instance):
        self.L = BasicPropositions("L")
        self.L = False #Lead is false unless tricks[3] is true(Team x won trick 3)

        if tricks_instance.tricks[3] == True: # checks if team x won trick 3
            self.L = True

@proposition(E)
class Card:
    def __init__(self, type, value, trick):
        self.C = BasicPropositions("C")
        self.card_type = card_type
        self.rank = rank
        self.trick_number = trick_number

    def is_winning(self):
        if self.card_type == 1:
            return self.rank in trumpRank and self.trick_number in [4,5]
        elif self.card_type == 2:
            return self.rank and self.trick_number in [4,5] # 
        else:
            return False # If the card is offsuit and not the suit that was led, it can't win

        


# Different classes for propositions are useful because this allows for more dynamic constraint creation
# for propositions within that class. For example, you can enforce that "at least one" of the propositions
# that are instances of this class must be true by using a @constraint decorator.
# other options include: at most one, exactly one, at most k, and implies all.
# For a complete module reference, see https://bauhaus.readthedocs.io/en/latest/bauhaus.html

@proposition(E)
class FancyPropositions:

    def __init__(self, data):
        self.data = data

    def _prop_name(self):
        return f"A.{self.data}"
    


@constraint.at_least_one(E)
@proposition(E)
def constraints():

    constraint_expression1 = C1_vprime | (~C1_vprime & C2_vprime)

    E.add_constraint(constraint_expression1)

    constraint_TeamX = T_TeamX >> (P1_c | P3_c)
    constraint_TeamY = T_TeamY >> (P2_c | P4_c)

    winning_card_constraint = constraint_TeamX & constraint_TeamY

    E.add_constraint(winning_card_constraint)


    # Construct the win conditions
    win_3_tricks = T1 & T2 & T3
    win_4_tricks = T1 & T2 & T3 & T4
    win_5_tricks = T1 & T2 & T3 & T4 & T5

    # Combine the possibilities
    win_round_condition = win_3_tricks | win_4_tricks | win_5_tricks

    # Express the equivalence between W and the win conditions
    win_round_equivalence = (W >> win_round_condition) & (win_round_condition >> W)
    E.add_constraint(win_round_equivalence)

    euchre_condition = (W & ~C) | (~W & C)

    # Ensure E is true if and only if the euchre condition holds
    euchre_equivalence = (E >> euchre_condition) & (euchre_condition >> E)
    E.add_constraint(euchre_equivalence)

    return E

# Build an example full theory for your setting and return it.
#
#  There should be at least 10 variables, and a sufficiently large formula to describe it (>50 operators).
#  This restriction is fairly minimal, and if there is any concern, reach out to the teaching staff to clarify
#  what the expectations are.
def example_theory():
    # # Add custom constraints by creating formulas with the variables you created. 
    # E.add_constraint((a | b) & ~x)
    # # Implication
    # E.add_constraint(y >> z)
    # # Negate a formula
    # E.add_constraint(~(x & y))
    # # You can also add more customized "fancy" constraints. Use case: you don't want to enforce "exactly one"
    # # for every instance of BasicPropositions, but you want to enforce it for a, b, and c.:
    # constraint.add_exactly_one(E, a, b, c)

    # return E


# if __name__ == "__main__":

#     T = example_theory()
#     # Don't compile until you're finished adding all your constraints!
#     T = T.compile()
#     # After compilation (and only after), you can check some of the properties
#     # of your model:
#     print("\nSatisfiable: %s" % T.satisfiable())
#     print("# Solutions: %d" % count_solutions(T))
#     print("   Solution: %s" % T.solve())

#     print("\nVariable likelihoods:")
#     for v,vn in zip([a,b,c,x,y,z], 'abcxyz'):
#         # Ensure that you only send these functions NNF formulas
#         # Literals are compiled to NNF here
#         print(" %s: %.2f" % (vn, likelihood(T, v)))
#     print()
