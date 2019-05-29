MACHINE Poker  
SETS 
	DECK={ACE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGTH,NINE,TEN,JACK,QUEEN,KING};
	SUITS={SPADES, HEARTS, DIAMONDS, CLUBS}

VARIABLES         
    playable_deck, comunity_cards, player_one_cards, player_two_cards

CONSTANTS         
    DUMMY
PROPERTIES
    DUMMY : DECK*SUITS
    
INVARIANT         
    playable_deck <: DECK*SUITS
    & comunity_cards <: DECK*SUITS 
    & player_one_cards <: DECK*SUITS 
    & player_two_cards <: DECK*SUITS 
    & card( comunity_cards ) <= 5
    & card( player_one_cards ) <= 2
    & card( player_two_cards ) <= 2
    & card(playable_deck /\ comunity_cards) = 0
    & card(playable_deck /\ player_one_cards) = 0
    & card(playable_deck /\ player_two_cards) = 0
    & card(comunity_cards /\ player_one_cards) = 0
    & card(comunity_cards /\ player_two_cards) = 0
    & card(player_one_cards /\ player_two_cards) = 0
    & ( card( playable_deck ) + card( comunity_cards ) + card( player_one_cards ) + card( player_two_cards ) )=52

INITIALISATION 
	playable_deck := DECK*SUITS || 
	comunity_cards :={} || 
	player_one_cards :={} || 
	player_two_cards :={}
	
OPERATIONS
  aa, bb, cc <-- deal_comunity_cards =
  PRE card(playable_deck) > 0 & card(comunity_cards) <= 4
  THEN 
	IF card(comunity_cards) = 0
	THEN
      ANY xx, yy, zz
      WHERE xx:DECK*SUITS & yy:DECK*SUITS & zz:DECK*SUITS & 
          {xx, yy, zz} <: playable_deck & card({xx, yy, zz}) = 3
      THEN playable_deck := playable_deck - {xx, yy, zz} || 
          comunity_cards := comunity_cards \/ {xx, yy, zz} ||
          aa := xx ||
          bb := yy ||
          cc := zz
      END
    ELSE
      ANY xx
      WHERE xx:DECK*SUITS & {xx} <: playable_deck
      THEN playable_deck := playable_deck - {xx} ||
          comunity_cards := comunity_cards \/ {xx} ||
          aa := xx ||
          bb := DUMMY ||
          cc := DUMMY
      END
	END
  END;

  aa, bb, cc, dd <-- deal_two_cards_to_two_players =
  	PRE card(playable_deck)>=4 & card(comunity_cards) = 3
 	THEN 
      ANY xx, yy, zz, kk
      WHERE xx:DECK*SUITS & yy:DECK*SUITS & zz:DECK*SUITS & kk:DECK*SUITS & 
          {xx, yy, zz, kk} <: playable_deck & card({xx, yy, zz, kk}) = 4
      THEN playable_deck := playable_deck - {xx, yy, zz, kk} || 
          player_one_cards := player_one_cards \/ {xx, yy} || 
          player_two_cards := player_two_cards \/ {zz, kk} ||
          aa := xx ||
          bb := yy ||
          cc := zz ||
          dd := kk 
      END
  END;

  aa <-- cardinalidade_deck = 
    aa := card( playable_deck );

  aa <-- cardinalidade_comunity = 
    aa := card( comunity_cards );

  aa <-- cardinalidade_player_one = 
    aa := card( player_one_cards );

  aa <-- cardinalidade_player_two = 
    aa := card( player_two_cards )
	
END
