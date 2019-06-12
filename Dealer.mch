/* Poker
 * Author: Esther
 */
MACHINE Dealer
EXTENDS Gambler

SETS
    DECK = {ACE,TWO,THREE,FOUR,FIVE,SIX,SEVEN,EIGTH,NINE,TEN,JACK,QUEEN,KING};
    SUITS = {SPADES, HEARTS, DIAMONDS, CLUBS}

VARIABLES
    playable_deck, comunity_cards, player_one_cards, player_two_cards, royal_flush
    
INVARIANT         
    playable_deck <: DECK*SUITS
    & comunity_cards <: DECK*SUITS 
    & player_one_cards <: DECK*SUITS 
    & player_two_cards <: DECK*SUITS 
    & card( comunity_cards ) <= 5
    & card( player_one_cards ) <= 2
    & card( player_two_cards ) <= 2
    & card( playable_deck /\ comunity_cards ) = 0
    & card( playable_deck /\ player_one_cards ) = 0
    & card( playable_deck /\ player_two_cards ) = 0
    & card( comunity_cards /\ player_one_cards ) = 0
    & card( comunity_cards /\ player_two_cards ) = 0
    & card( player_one_cards /\ player_two_cards ) = 0
    & ( card( playable_deck ) + card( comunity_cards ) + card( player_one_cards ) + card( player_two_cards ) )=52
    & royal_flush <: DECK

INITIALISATION 
    playable_deck := DECK*SUITS || 
    comunity_cards :={} || 
    player_one_cards :={} || 
    player_two_cards :={} ||
    royal_flush := {ACE,TEN,JACK,QUEEN,KING}
	
OPERATIONS

/****** dealer ******/
  deal_comunity_cards =
  PRE gambleTime = NO & card( playable_deck ) > 3 & card( comunity_cards ) = 0
  THEN
      	ANY xx, yy, zz
      	WHERE xx:DECK*SUITS & yy:DECK*SUITS & zz:DECK*SUITS & 
         	 	{xx, yy, zz} <: playable_deck & card( {xx, yy, zz} ) = 3
      	THEN 	playable_deck := playable_deck - {xx, yy, zz} || 
          		comunity_cards := comunity_cards \/ {xx, yy, zz}
      	END 
      	||
      	startGambleTime
  END;
  
  /*
  deal_comunity_cards_robado =
  PRE gambleTime = NO & 
    card( playable_deck ) > 3 & card( comunity_cards ) = 0
  THEN 	
  	playable_deck := playable_deck - {ACE}*{SPADES, HEARTS, DIAMONDS} ||
  	comunity_cards := comunity_cards \/ {ACE}*{SPADES, HEARTS, DIAMONDS} ||
    gambleTime := YES
  END;
  */

  deal_one_comunity_card =
  PRE gambleTime = NO & 
	card(comunity_cards) >=3 & card(comunity_cards) <= 4 & 
	card( player_one_cards ) > 0 & card( player_two_cards ) > 0 & 
	card(playable_deck) >= 1
  THEN 
      ANY xx
      WHERE xx:DECK*SUITS & {xx} <: playable_deck
      THEN playable_deck := playable_deck - {xx} ||
          comunity_cards := comunity_cards \/ {xx}
      END ||
      IF card(comunity_cards) = 3 //Theres still one gambling round left
      THEN startGambleTime
      END
  END;
  
  /*
  deal_two_cards_to_two_players_robado =
  PRE gambleTime = NO & card( player_one_cards ) = 0 & card( player_two_cards ) = 0 & card(playable_deck)>=4 & card(comunity_cards) = 3
  THEN 
  	playable_deck := playable_deck - {ACE}*{CLUBS} ||
  	player_one_cards := player_one_cards \/ {ACE}*{HEARTS} \/ {TWO}*{HEARTS} ||
  	player_two_cards := player_two_cards \/ {ACE}*{CLUBS} \/ {TWO}*{HEARTS} ||
    gambleTime := YES
  END;
  */

   deal_two_cards_to_two_players =
  PRE gambleTime = NO & card( player_one_cards ) = 0 & card( player_two_cards ) = 0 & card(playable_deck)>=4 & card(comunity_cards) = 3
  THEN 
      ANY xx, yy, zz, kk
      WHERE xx:DECK*SUITS & yy:DECK*SUITS & zz:DECK*SUITS & kk:DECK*SUITS & 
          	{xx, yy, zz, kk} <: playable_deck & card( {xx, yy, zz, kk} ) = 4
      THEN playable_deck := playable_deck - {xx, yy, zz, kk} || 
          player_one_cards := player_one_cards \/ {xx, yy} || 
          player_two_cards := player_two_cards \/ {zz, kk}
      END ||
      startGambleTime
  END;
/****** end dealer ******/


/****** combos ******/
  	ww <-- royal_flush_winner =
  	PRE ww:INGAME & card( player_one_cards ) = 2 & card( player_two_cards ) = 2 & card( comunity_cards ) = 5
  	THEN 
  		IF  
      		royal_flush *{SPADES} <: player_one_cards \/ comunity_cards  or
    		royal_flush *{HEARTS} <: player_one_cards \/ comunity_cards or
    		royal_flush *{DIAMONDS} <: player_one_cards \/ comunity_cards or
    		royal_flush *{CLUBS} <: player_one_cards \/ comunity_cards
  		THEN
  			ww:=P_ONE
  		ELSE
  			IF 
       			 royal_flush *{SPADES} <: player_two_cards \/ comunity_cards or
    			royal_flush *{HEARTS} <: player_two_cards \/ comunity_cards  or
    			royal_flush *{DIAMONDS} <: player_two_cards \/ comunity_cards  or
    			royal_flush *{CLUBS} <: player_two_cards \/ comunity_cards 
			THEN
				ww:=P_TWO
			ELSE
				ww:=P_NONE
			END
		END
  END;

	ww <-- quadra_winner =
		PRE ww:INGAME & card( player_one_cards ) = 2 & card( player_two_cards ) = 2 & card( comunity_cards ) = 5
		THEN 
			IF 
				{ACE} *SUITS <: player_one_cards \/ comunity_cards or
				{TWO } *SUITS <: player_one_cards \/ comunity_cards or
				{THREE} *SUITS <: player_one_cards \/ comunity_cards or
				{FOUR} *SUITS <: player_one_cards \/ comunity_cards  or
				{FIVE} * SUITS <: player_one_cards \/ comunity_cards or
				{SIX} *SUITS <: player_one_cards \/ comunity_cards or
				{EIGTH} * SUITS <: player_one_cards \/ comunity_cards or
				{NINE} * SUITS <: player_one_cards \/ comunity_cards or
				{TEN} * SUITS <: player_one_cards \/ comunity_cards or
				{JACK} * SUITS <: player_one_cards \/ comunity_cards or
				{QUEEN} * SUITS <: player_one_cards \/ comunity_cards or
				{KING} * SUITS <: player_one_cards \/ comunity_cards
			THEN
				ww:=P_ONE
			ELSE
				IF 
					{ACE} *SUITS <: player_two_cards \/ comunity_cards or
					{TWO } *SUITS <: player_two_cards \/ comunity_cards  or
					{THREE} *SUITS <: player_two_cards \/ comunity_cards  or
					{FOUR} *SUITS <: player_two_cards \/ comunity_cards   or
					{FIVE} * SUITS <: player_two_cards \/ comunity_cards  or
					{SIX} *SUITS <: player_two_cards \/ comunity_cards  or
					{EIGTH} * SUITS <: player_two_cards \/ comunity_cards  or
					{NINE} * SUITS <: player_two_cards \/ comunity_cards  or
					{TEN} * SUITS <: player_two_cards \/ comunity_cards  or
					{JACK} * SUITS <: player_two_cards \/ comunity_cards  or
					{QUEEN} * SUITS <: player_two_cards \/ comunity_cards  or
					{KING} * SUITS <: player_two_cards \/ comunity_cards 
				THEN
					ww:=P_TWO
				ELSE
					ww:=P_NONE
			END
		END
	END
/****** end combos ******/

/****** values ******/
/*
  aa <-- cardinalidade_deck = 
    aa := card( playable_deck );

  aa <-- cardinalidade_comunity = 
    aa := card( comunity_cards );

  aa <-- cardinalidade_player_one = 
    aa := card( player_one_cards );

  aa <-- cardinalidade_player_two = 
    aa := card( player_two_cards )
*/
/****** end values ******/

END
