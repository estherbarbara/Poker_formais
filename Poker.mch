MACHINE Poker  
SETS 
	DECK={ACE,ONE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGTH,NINE,TEN,JACK,QUEEN,KING};
	SUITS={SPADES, HEARTS, DIAMONDS, CLUBS} 
VARIABLES         
    playable_deck, comunity_cards, player_one_cards, player_two_cards
INVARIANT         
    playable_deck <: DECK*SUITS
    & comunity_cards <: DECK*SUITS 
    & player_one_cards <: DECK*SUITS 
    & player_two_cards <: DECK*SUITS 
    & (card(playable_deck) + card(comunity_cards) + card(player_one_cards) + card(player_two_cards))=52
INITIALISATION 
	playable_deck := DECK*SUITS || 
	comunity_cards:={} || 
	player_one_cards:={} || 
	player_two_cards:={}
OPERATIONS
  aa, bb, cc <-- deal_comunity_cards =
  PRE card(playable_deck)>1
  THEN 
    aa :: playable_deck; playable_deck:= playable_deck-{aa};
    bb :: playable_deck; playable_deck:= playable_deck-{bb};
    cc :: playable_deck; playable_deck:= playable_deck-{cc}
  END;

  aa, bb, cc, dd <-- deal_two_cards_to_players =
  PRE card(playable_deck)>1
  THEN 
    aa :: playable_deck; playable_deck:= playable_deck-{aa};
    bb :: playable_deck; playable_deck:= playable_deck-{bb};
    cc :: playable_deck; playable_deck:= playable_deck-{cc};
    dd :: playable_deck; playable_deck:= playable_deck-{dd}
  END;

  aa <-- card_mesa = 
    aa := card(playable_deck) + card(comunity_cards) + card(player_one_cards) + card(player_two_cards)
	
END