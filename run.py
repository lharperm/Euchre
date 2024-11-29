
from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood

import random

# These two lines make sure a faster SAT solver is used.
from nnf import config
config.sat_backend = "kissat"

'''
The following code initiates the teams, players, and their cards
for our model. 
'''

'''
teams dictionary stores values for cards and  players
for their respective teams X and Y. TeamX consists of payers 1
and 3, and Team Y consists of players 2 and 4
'''
teams = {    
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
}    

'''
Initiation of the deck consisting of four suits,
each suit consists of cards 1-6 representing
9, 10, jack, queen, king, ace.
'''
deck = {
    "hearts": [1, 2, 3, 4, 5, 6],
    "diamonds": [1, 2, 3, 4, 5, 6],
    "spades": [1, 2, 3, 4, 5, 6],
    "clubs": [1, 2, 3, 4, 5, 6]
}

'''
suitMap assigns each suit a respective value.
'''
suitMap = {1: "hearts", 2: "diamonds", 3: "spades", 4: "clubs"}

'''
deal(deck) populates players hands to generate the
starting conditions of the model. It randomly deals and
ensures that no player is dealt a duplicate card
'''
def deal(deck):
    while True:
        suit = suitMap[random.randint(1, 4)]    #Map random number to suit
        v = random.randint(1, 6)  #Randomly pick a value

        if v in deck[suit]:      #Check card is still in deck 
            deck[suit].remove(v)     #Update deck
            return suit, v  
    

'''
Card map is initiated to make the deal process faster. 
'''
cardMap = [
    ("teamX", "player1", "card1"),
    ("teamY", "player2", "card1"),
    ("teamX", "player3", "card1"),
    ("teamY", "player4", "card1"),
    ("teamX", "player1", "card2"),
    ("teamY", "player2", "card2"),
    ("teamX", "player3", "card2"),
    ("teamY", "player4", "card2")
]

'''
Using cardMap, loop iterates over each player and their cards.
For each card, it calls deal to generate a random card and popualtes
each players hand
'''
for team, player, card in cardMap:
    suit, value = deal(deck)
    teams[team][player][card]["type"] = suit
    teams[team][player][card]["value"] = value

'''
Randomly assingn 0 for teamX and 1 for teamY as input to the model 
since our model is focused on the remaining two tricks in play.
'''

tricks = []
i = 1
while i <= 3:
    j = random.randint(0,1)

    if j == 0: 
        tricks.append(True)
    else:
        tricks.append(False)

'''
Map for left_bower values. 
'''
left_bower = {   
    "hearts": "diamonds",
    "diamonds": "hearts",
    "spades": "clubs",
    "clubs": "spades"
}

'''
The following code consists of our propositions and constraints.
'''

# Encoding that stores constraints
E = Encoding()

@proposition(E)
class BasicPropositions:

    def __init__(self, data):
        self.data = data

    def _prop_name(self):
        return f"A.{self.data}"
    

'''Define variables.'''

C1_vprime = BasicPropositions("C1_vprime")  
C2_vprime = BasicPropositions("C2_vprime")  


'''propositions for players holding the winning card.'''
P1_c = BasicPropositions("P1_c")
P2_c = BasicPropositions("P2_c")
P3_c = BasicPropositions("P3_c")
P4_c = BasicPropositions("P4_c")

'''Propositions for teams holding the winning trick.'''
T_TeamX = BasicPropositions("T_TeamX")
T_TeamY = BasicPropositions("T_TeamY")

T1 = BasicPropositions("T1")
T2 = BasicPropositions("T2")
T3 = BasicPropositions("T3")
T4 = BasicPropositions("T4")
T5 = BasicPropositions("T5")

'''Propositions for determining hiearchy.'''
@proposition(E)
class TrumpSuit:
    def __init__(self, suit):
        self.suit = suit 

class IsLeftBower:
    def __init__(self, suit, team, player, card):
        self.left_bower_suit = left_bower[suit]  
        self.card_suit = teams[team][player][card]["type"]  
        self.card_value = teams[team][player][card]["value"]  

    def is_left_bower(self):
        return self.card_suit == self.left_bower_suit and self.card_value == 3

class RightBower:
    def __init__(self, trump_suit, team, player, card):
        self.trump_suit = trump_suit
        self.card_suit = teams[team][player][card]["type"]
        self.card_value = teams[team][player][card]["value"]

    def is_right_bower(self):
        return self.card_suit == self.trump_suit and self.card_value == 3
    
'''Propositions for determining trump if a card played is trump.'''   
@proposition(E)
class IsTrump:
    def __init__(self, trump_suit, team, player, card):
        self.trump_suit = trump_suit  
        self.card_suit = teams[team][player][card]["type"]  
        self.is_left_bower = IsLeftBower(trump_suit, team, player, card)  

    def is_trump(self):
        return self.card_suit == self.trump_suit or self.is_left_bower.is_left_bower()
    
'''Propositions for which player called trump.'''  
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

'''Propositions for defining the winning team of a trick.''' 
@proposition(E)           
class TrickWinner:
    def __init__(self, trick_number, winning_team):
        self.trick_number = trick_number
        self.winning_team = winning_team  # "teamX" or "teamY"

    def __str__(self):
        return f"Trick {self.trick_number}: Winner - {self.winning_team}"
   
'''Propositions for defining the winning team of a round.''' 
@proposition(E)
class Win:
    def __init__(self, tricks_instance):

        #Define propositions for winning conditions (winning 3, 4, or 5 tricks)
        self.W3 = BasicPropositions("W3")
        self.W4 = BasicPropositions("W4")
        self.W5 = BasicPropositions("W5")

        #Count the number of tricks won by team X using the tricks dictionary from the Tricks instance
        x_wins = 0
        for val in tricks_instance:
            if val == True:
                x_wins += 1

        self.W3 = (x_wins >= 3)
        self.W4 = (x_wins >= 4)
        self.W5 = (x_wins == 5)


        #Define Win_Wt as the logical OR of W3, W4, and W5
        self.Win_Wt = self.W3 | self.W4 | self.W5

'''Propositions for defining whether or not a Euchre takes place''' 
@proposition(E)
class Euchre:
    def __init__(self, win_instance, trump_instance):
        
        self.W = win_instance.win_Wt
        self.C = trump_instance.Q

        #Define Euchre condition: E is True if W is false and C is true
        self.E = self.C & ~self.W

'''Propositions for defining the suit for a trick''' 
@proposition(E)
class IsSuit:
    def __init__(self, team, player, card, lead_suit):
        self.card_suit = teams[team][player][card]["type"]  # Get the suit from the teams dictionary
        self.lead_suit = lead_suit  # Lead suit for the current trick

    def is_on_suit(self):
        # Return True only if the current card's suit matches the lead suit
        return self.card_suit == self.lead_suit
    
'''Propositions for determining the winning card of a trick.'''
@proposition(E)
class WinningCard:
    def __init__(self, trick_number, team, player, card):
        self.trick_number = trick_number
        self.team = team
        self.player = player
        self.card = card
        self.card_suit = teams[team][player][card]["type"]
        self.card_value = teams[team][player][card]["value"]
        self.is_trump = IsTrump(self.card_suit, team, player, card).is_trump()
        self.is_left_bower = IsLeftBower(self.card_suit, team, player, card).is_left_bower()
        self.is_right_bower = RightBower(self.card_suit, team, player, card).is_right_bower()

    def wins_trick(self, current_trick_cards, trump_suit, lead_suit):
        highest_trump = None
        highest_lead = None

        #Evaluate trump cards
        for c in current_trick_cards:
            if IsTrump(trump_suit, c["team"], c["player"], c["card"]).is_trump():
                if not highest_trump or c["value"] > highest_trump["value"]:
                    highest_trump = c

        #If no trump cards are played, evaluate lead suit cards
        if not highest_trump:
            for c in current_trick_cards:
                if c["suit"] == lead_suit:
                    if not highest_lead or c["value"] > highest_lead["value"]:
                        highest_lead = c

        #Determine if this card wins
        return (
            (highest_trump and self.card == highest_trump["card"]) or
            (not highest_trump and highest_lead and self.card == highest_lead["card"])
        )


'''Propositions for defining the player with the winning card for a trick''' 
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

'''Propositions for defining which player leads on trick4''' 
@proposition(E)
class Lead:
    def __init__(self, tricks_instance):
        self.L = BasicPropositions("L")
        self.L = False #Lead is false unless tricks[3] is true(Team x won trick 3)

        if tricks_instance.tricks[3] == True: # checks if team x won trick 3
            self.L = True

'''Propositions for defining the winning team of a trick.''' 
@proposition(E)
class Card:
    def __init__(self, card_type, rank, trick_number):
        self.C = BasicPropositions("C")
        self.card_type = card_type
        self.rank = rank
        self.trick_number = trick_number

    def is_winning(self, trump_rank, lead_suit):
        if self.card_type == "trump":
            return self.rank in trump_rank
        elif self.card_type == lead_suit:
            return True  # Follow-suit wins if no trump is played
        else:
            return False  # Off-suit cards lose

'''The following code is for the constraints on our model.'''

W = BasicPropositions("W")
C = BasicPropositions("C")

@constraint.at_least_one(E)
@proposition(E)
def constraints():
    # Example initial constraints
    constraint_expression1 = C1_vprime | (~C1_vprime & C2_vprime)
    E.add_constraint(constraint_expression1)

    constraint_TeamX = T_TeamX >> (P1_c | P3_c)
    constraint_TeamY = T_TeamY >> (P2_c | P4_c)

    winning_card_constraint = constraint_TeamX & constraint_TeamY
    E.add_constraint(winning_card_constraint)

    # Construct win conditions
    win_3_tricks = T1 & T2 & T3
    win_4_tricks = T1 & T2 & T3 & T4
    win_5_tricks = T1 & T2 & T3 & T4 & T5

    # Combine the possibilities
    win_round_condition = win_3_tricks | win_4_tricks | win_5_tricks

    # Express equivalence between W and win conditions
    win_round_equivalence = (W >> win_round_condition) & (win_round_condition >> W)
    E.add_constraint(win_round_equivalence)

    # Euchre conditions
    euchre_condition = (W & ~C) | (~W & C)
    euchre_equivalence = (E >> euchre_condition) & (euchre_condition >> E)
    E.add_constraint(euchre_equivalence)

    # Ensure exactly one team wins each trick
    for trick in [T1, T2, T3, T4, T5]:
        E.add_constraint(trick >> (T_TeamX | T_TeamY))
        E.add_constraint(~(T_TeamX & T_TeamY))

    #Ensures player follows suit and plays a valid card.
    for team in teams:
        for player in teams[team]:
            for card in teams[team][player]:
                card_played = teams[team][player][card]

                #chek card follows suit
                follows_suit = IsSuit(team, player, card, lead_suit=True).is_on_suit()  
                
                #chekc if player has a card of the same suit as lead suit.

                has_lead_suit = False
                for c in teams[team][player]:
                    if IsSuit(team, player, c, lead_suit=True).is_on_suit():
                        has_lead_suit = True
                        break

                # Add constraint: If a card is played, it must follow the lead suit if the lead suit exists and the player has a card in that suit
                E.add_constraint(card_played >> ((~has_lead_suit) | follows_suit))
    """
    Implement winning card constraint here
    """

    """
    Implment winning team constraint here
    """

    """
    Implement euchre constraint here
    """

    return E

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
