from bauhaus import Encoding, proposition, constraint
from bauhaus.utils import count_solutions, likelihood

from nnf import config

import random

'''
The following code initiates the teams, players, and their cards
for our model. 
'''

'''
teams dictionary stores values for cards and  players
for their respective teams X and Y. TeamX consists of payers 1
and 3, and Team Y consists of players 2 and 4. Imagine at table:

player 3 player 4
    table
player 2 player 1
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


def shuffle_deck(deck):
    # Flatten the deck into a list of (suit, value) tuples
    flat_deck = [(suit, value) for suit in deck for value in deck[suit]]
    random.shuffle(flat_deck)  # Shuffle the list
    return flat_deck
'''
deal(deck) populates players hands to generate the
starting conditions of the model. It randomly deals and
ensures that no player is dealt a duplicate card
'''
def deal(shuffled_deck):
    if not shuffled_deck:
        raise ValueError("The deck is empty! Cannot deal more cards.")
    return shuffled_deck.pop(0)

"""
Deals cards to all players, ensuring no duplicate cards.
 """
def deal_to_players(teams, shuffled_deck):
    card_map = [
        ("teamX", "player1", "card1"),
        ("teamY", "player2", "card1"),
        ("teamX", "player3", "card1"),
        ("teamY", "player4", "card1"),
        ("teamX", "player1", "card2"),
        ("teamY", "player2", "card2"),
        ("teamX", "player3", "card2"),
        ("teamY", "player4", "card2")
    ]
    for team, player, card in card_map:
        suit, value = deal(shuffled_deck)
        teams[team][player][card]["type"] = suit
        teams[team][player][card]["value"] = value

value_to_card = {
        1: "Nine",
        2: "Ten",
        3: "Jack",
        4: "Queen",
        5: "King",
        6: "Ace"
    }

"""
Prints each player's hand for testing
"""   
def print_player_hands(teams):
    for team in teams:
        print(f"\n{team.capitalize()} Hands:")
        for player in teams[team]:
            cards = teams[team][player]
            card1_value = value_to_card[cards['card1']['value']]  # Map value to card name
            card2_value = value_to_card[cards['card2']['value']]  # Map value to card name
            card1 = f"{card1_value} of {cards['card1']['type'].capitalize()}"
            card2 = f"{card2_value} of {cards['card2']['type'].capitalize()}"
            print(f"  {player.capitalize()}: {card1}, {card2}")

'''
Randomly assingn 0 for teamX and 1 for teamY as input to the model 
since our model is focused on the remaining two tricks in play.
'''
def gen_tricks():
    tricks = []
    i = 1
    while i <= 3:
        j = random.randint(0,1)

        if j == 0: 
            tricks.append(True)
        else:
            tricks.append(False)
        i += 1
    return tricks

def print_tricks(tricks):
    xwins = 0
    ywins = 0
    for val in tricks:
        if val == 1:
            xwins += 1
        else:
            ywins += 1
    print(f"  TeamX has won {xwins} tricks.")
    print(f"  TeamY has won {ywins} tricks.")

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
class CalledTrump:
    def __init__(self):
        self.i = random.randint(0, 1)  # Randomly determine if trump is called
        self.Q = BasicPropositions("Q") if self.i == 1 else BasicPropositions("¬Q")

    def _prop_name(self):
        return f"CalledTrump({self.i})"

@proposition(E)
class BasicPropositions:
    def __init__(self, name):
        self.name = name

    def _prop_name(self):
        return f"Prop({self.name})"
    
@proposition(E)
class TrumpSuit:
    def __init__(self, suit):
        self.suit = suit 

    def _prop_name(self):
        return f"TrumpSuit({self.suit})"

@proposition(E)
class IsLeftBower:
    def __init__(self, suit, team, player, card):
        self.suit = suit  # Assign suit as an instance attribute
        self.team = team  # Assign team as an instance attribute
        self.player = player  # Assign player as an instance attribute
        self.card = card  # Assign card as an instance attribute

        self.left_bower_suit = left_bower[suit]  
        self.card_suit = teams[team][player][card]["type"]  
        self.card_value = teams[team][player][card]["value"] 
      


    def is_left_bower(self):
        return BasicPropositions(f"LeftBower({self.team}, {self.player}, {self.card})")
    
    def _prop_name(self):
        return f"LeftBower({self.trump_suit}, {self.team}, {self.player}, {self.card})"

@proposition(E)
class RightBower:
    def __init__(self, trump_suit, team, player, card):
        self.trump_suit = trump_suit  # Assign trump_suit as an instance attribute
        self.team = team  # Assign team as an instance attribute
        self.player = player  # Assign player as an instance attribute
        self.card = card  # Assign card as an instance attribute

        self.card_suit = teams[team][player][card]["type"]
        self.card_value = teams[team][player][card]["value"]

    def is_right_bower(self):
        return BasicPropositions(f"RightBower({self.team}, {self.player}, {self.card})")
    
    def _prop_name(self):
        return f"RightBower({self.trump_suit}, {self.team}, {self.player}, {self.card})"
    
@proposition(E)
class Lead:
    def __init__(self, tricks, winning_card):

        self.tricks = tricks 
        if len(tricks) == 3:
            self.trick_number = 4
        else:
            self.trick_number = 5

        self.lead_player = None
        self.winning_team = None
        self.L = None 

        if self.trick_number == 4:
            if self.tricks[2] == 1:
                self.winning_team = "teamX"
            else:
                self.winning_team = "teamY"
            
            self.lead_player = random.choice(list(teams[self.winning_team].keys()))
            self.L = BasicPropositions(f"Lead(Trick 4, {self.lead_player})")
                
        if self.trick_number == 5:
            self.winning_team = winning_card["team"]
            self.lead_player = winning_card["player"]

            # Define the lead proposition
            self.L = BasicPropositions(f"Lead(Trick 5, {self.lead_player})")

    def _prop_name(self):
        return f"Lead({self.L})"
'''Propositions for defining the suit for a trick''' 
@proposition(E)
class IsSuit:
    def __init__(self, team, player, card, lead_suit):
        self.team = team
        self.player = player
        self.card = card
        self.card_suit = teams[team][player][card]["type"]  # Get the suit from the teams dictionary
        self.lead_suit = lead_suit  # Lead suit for the current trick

    def is_on_suit(self):
        return self.card_suit == self.lead_suit  # Return True if the card matches the lead suit

    def _prop_name(self):
        return f"IsSuit({self.team}, {self.player}, {self.card}, {self.lead_suit})"
    
@proposition(E)
class WinningCard:
    def __init__(self, played_card):
        self.team = played_card["team"]
        self.player = played_card["player"]
        self.card = played_card["card"]
        self.card_suit = played_card["card"]["type"]
        self.card_value = played_card["card"]["value"]

    def is_winning_card(self, current_winner, trump_suit, lead_suit):
        # Check Right Bower
        if self.card_suit == trump_suit and self.card_value == 3:
            return True  # Right Bower automatically wins
        
        # Check Left Bower
        if left_bower[trump_suit] == self.card_suit and self.card_value == 3:
            if current_winner and current_winner.card_suit == trump_suit and current_winner.card_value == 3:
                return False  # Right Bower beats Left Bower
            return True

        # Check Trump Suit
        if self.card_suit == trump_suit:
            if current_winner and current_winner.card_suit == trump_suit:
                return self.card_value > current_winner.card_value
            return True

        # Check Lead Suit
        if self.card_suit == lead_suit:
            if current_winner and current_winner.card_suit == lead_suit:
                return self.card_value > current_winner.card_value
            return True

        return False

    def _prop_name(self):
        return f"WinningCard({self.team}, {self.player}, {self.card})"
    
'''Propositions for defining whether or not a Euchre takes place''' 
@proposition(E)
class Euchre:
    def __init__(self, W, C):

        self.W = W
        self.C = C
        self.E = (self.W & ~self.C) | (~self.W & self.C)

    def add_constraint(self):
        """
        Add the Euchre equivalence constraint to the encoding.
        """
        E_euchre = BasicPropositions("Euchre")
        euchre_equivalence = (E_euchre >> self.E) & (self.E >> E_euchre)
        E.add_constraint(euchre_equivalence)
        print(f"Euchre condition: (W & ~C): {self.W & ~self.C}, (~W & C): {~self.W & self.C}")
        print(f"Euchre proposition: {self.E}")

    def _prop_name(self):
        return f"Euchre({self.W}, {self.C})"

'''Propositions for defining the winning team of a round.''' 
@proposition(E)
class Win:
    def __init__(self, tricks_instance):
        self.tricks_instance = tricks_instance

        # Define propositions for winning conditions (winning 3, 4, or 5 tricks)
        self.W3 = BasicPropositions("W3")
        self.W4 = BasicPropositions("W4")
        self.W5 = BasicPropositions("W5")

    def _prop_name(self):
        return f"Win({self.tricks_instance})"
    
@proposition(E)
class WinningCardForPlayer:
    def __init__(self, player, card):
        self.player = player
        self.card = card

    def _prop_name(self):
        return f"WinningCard({self.player}, {self.card})"

def win_constraints(tricks):
    # Count the number of tricks won by TeamX
    team_x_wins = sum(1 for trick in tricks if trick == 1)

    # Define W as True if TeamX wins 3 or more tricks
    W = BasicPropositions("W") if team_x_wins >= 3 else ~BasicPropositions("W")

    # Debug print to verify the trick count and W value
    print(f"TeamX won {team_x_wins} tricks. W is {'True' if team_x_wins >= 3 else 'False'}.")

    # Add constraint for W (TeamX winning condition)
    E.add_constraint(W)
    return W
    
def example_theory():
    """
    Minimal working model to test compilation.
    """
    global teams, deck

    shuffled_deck = shuffle_deck(deck)  # Shuffle the deck
    deal_to_players(teams, shuffled_deck)  # Deal cards to players
    print_player_hands(teams)  # Print players' hands for verification
    # Define basic propositions
    trump_suit = "spades"  #change for different versions of model
    trump = TrumpSuit(trump_suit)
    E.add_constraint(trump)

   

    tricks = gen_tricks() #generate first 3 tricks
    print(f"\nInitial Tricks:")
    print_tricks(tricks)

    called = CalledTrump()
    C = BasicPropositions("C") if called.i == 1 else ~BasicPropositions("C")

    print("")
    if called.i == 1:
        print(f"Called: TeamX called trump")
    else:
        print(f"Called: TeamY called trump")

    print(f"Trump Suit: {trump_suit.capitalize()}")
    # Add constraints using the propositions themselves 
    for team, players in teams.items():
        for player, cards in players.items():
            for card_name, card in cards.items():
                # Check if the card is the Right Bower
                right_bower = RightBower(trump_suit, team, player, card_name)
                E.add_constraint(right_bower.is_right_bower())

                # Check if the card is the Left Bower
                left_bower = IsLeftBower(trump_suit, team, player, card_name)
                E.add_constraint(left_bower.is_left_bower())

    '''
    Trick 4 Gameplay
    '''
    lead4 = Lead(tricks=tricks, winning_card=None)
    print(f"Trick 4 Lead: {lead4.lead_player.capitalize()}")
    print("")

    lead_team = "teamX" if lead4.lead_player in teams["teamX"] else "teamY"
    lead_card_name = "card1"  
    lead_card = teams[lead_team][lead4.lead_player][lead_card_name]
    lead_suit = lead_card["type"]
    
    ordered_players = ["player1", "player2", "player3", "player4"]
    start_index = ordered_players.index(lead4.lead_player)
    ordered_play = ordered_players[start_index:] + ordered_players[:start_index]  # Rotate to start with lead player

    lead_team = "teamX" if lead4.lead_player in teams["teamX"] else "teamY"
    lead_card_name = "card1"  
    lead_card = teams[lead_team][lead4.lead_player][lead_card_name]
    lead_suit = lead_card["type"]

    print("Play: \n")
    print(f"{lead4.lead_player.capitalize()} plays {value_to_card[lead_card['value']]} of {lead_suit.capitalize()} as the lead card.")

    # Initialize played cards with the lead card
    # Trick 4 Gameplay
    played_cards = [{"team": lead_team, "player": lead4.lead_player, "card_name": lead_card_name, "card": lead_card}]
    teams[lead_team][lead4.lead_player].pop(lead_card_name)  # Remove the lead card from the player's hand

    for player in ordered_play[1:]:
        team = "teamX" if player in teams["teamX"] else "teamY"
        cards = teams[team][player]

        for card_name, card in cards.items():
            if IsSuit(team, player, card_name, lead_suit).is_on_suit():
                played_cards.append({"team": team, "player": player, "card_name": card_name, "card": card})
                teams[team][player].pop(card_name)  # Remove the card from the player's hand
                print(f"{player.capitalize()} plays {value_to_card[card['value']]} of {card['type'].capitalize()}.")
                break
        else:
            card_name, card = next(iter(cards.items()))
            played_cards.append({"team": team, "player": player, "card_name": card_name, "card": card})
            teams[team][player].pop(card_name)  # Remove the card from the player's hand
            print(f"{player.capitalize()} plays {value_to_card[card['value']]} of {card['type'].capitalize()}.")


        # Determine the winning card for the trick after all cards are played
    winning_card = None
    for played_card in played_cards:
        card_team = played_card["team"]
        card_player = played_card["player"]
        card_info = played_card["card"]
        current_card = WinningCard({"team": card_team, "player": card_player, "card": card_info})
        if winning_card is None or current_card.is_winning_card(winning_card, trump_suit, lead_card["type"]):
            winning_card = current_card

    # Output the winner after all cards are played
    print(f"\nTrick 4 Winner: {winning_card.player.capitalize()} from {winning_card.team.capitalize()} "
        f"with {value_to_card[winning_card.card['value']]} of {winning_card.card['type'].capitalize()}.")

    if winning_card.team == "teamX":
        tricks.append(1)
    else:
        tricks.append(0)

    """
    Trick 5 Gameplay
    """
    # Use the winner of Trick 4 to determine the lead player for Trick 5
    lead_player = winning_card.player  # Ensure lead_player is set correctly

    print(f"\nTrick 5 Lead: {lead_player.capitalize()}\n")

    # Rotate the order of play to start with the lead player
    ordered_players = ["player1", "player2", "player3", "player4"]
    start_index = ordered_players.index(lead_player)
    ordered_play = ordered_players[start_index:] + ordered_players[:start_index]  # Rotate to start with lead player

    # Initialize played cards list
    played_cards = []

    for player in ordered_play:
        team = "teamX" if player in teams["teamX"] else "teamY"
        cards = teams[team][player]
        
        # Play the only remaining card
        if cards:  # Ensure player still has cards
            remaining_card_name = list(cards.keys())[0]  # Get the name of the only card
            remaining_card = cards.pop(remaining_card_name)  # Remove the card from the player's hand
            played_cards.append({"team": team, "player": player, "card_name": remaining_card_name, "card": remaining_card})
            print(f"{player.capitalize()} plays {value_to_card[remaining_card['value']]} of {remaining_card['type'].capitalize()}.")
        else:
            print(f"{player.capitalize()} has no cards left to play!")

    # Determine the winning card for Trick 5
    winning_card = None
    for played_card in played_cards:
        card_team = played_card["team"]
        card_player = played_card["player"]
        card_info = played_card["card"]
        current_card = WinningCard({"team": card_team, "player": card_player, "card": card_info})
        if winning_card is None or current_card.is_winning_card(winning_card, trump_suit, played_cards[0]["card"]["type"]):
            winning_card = current_card

    # Output the winner of Trick 5
    print(f"\nTrick 5 Winner: {winning_card.player.capitalize()} from {winning_card.team.capitalize()} "
        f"with {value_to_card[winning_card.card['value']]} of {winning_card.card['type'].capitalize()}.")

    if winning_card.team == "teamX":
        tricks.append(1)
    else:
        tricks.append(0)

    win_instance = Win(tricks_instance=tricks)
    E.add_constraint(win_instance.W3)  # Add W3 proposition as a constraint
    print(f"Win instance created with tricks: {tricks}")

    W = win_constraints(tricks)
    euchre = Euchre(W, C)
    euchre.add_constraint()

    print("\nFinal trick results:")
    print_tricks(tricks)
    print("")

    print(f"W (TeamX won 3+ tricks): {W}")
    print(f"C (TeamX called trump): {C}")
   
    return E


if __name__ == "__main__":
   
    T = example_theory()  # Get the compiled theory
    T = T.compile()
    # Check satisfiability and print results
    satisfiable = T.satisfiable()
    if satisfiable:
        solution = T.solve()
        
        print("")

        # Check for Euchre
        euchre_status = solution.get(BasicPropositions("Euchre"), False)
        if euchre_status:
            print("A Euchre took place!")
        else:
            print("A Euchre did not take place.")
    print("\ncompiled succesfully")
    print("")
    print("Example solution:", solution)
