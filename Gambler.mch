/* Gambler
 * Author: Esther
 */
MACHINE Gambler  
SETS 
  	BOOLEAN = {YES, NO};
	INGAME = {P_ONE, P_TWO}

VARIABLES 
    playerOneTurn, playersInGame, gambleTime, 
    pool, first_player_raised_bet, bet_value_player_one, bet_value_player_two, actual_bet, first_round,
    first_player_money, second_player_money
    
INVARIANT
    playerOneTurn : BOOLEAN
    & gambleTime : BOOLEAN
    & first_round : BOOLEAN
    & playersInGame <: INGAME
    & pool : NAT
    & first_player_raised_bet : BOOLEAN
    & bet_value_player_one : NAT
    & bet_value_player_two : NAT
    & actual_bet : NAT
    & first_player_money : INT
    & second_player_money : INT

INITIALISATION 
	playerOneTurn := YES ||
	playersInGame := {P_ONE, P_TWO} ||
	gambleTime := YES ||
	pool := 0 ||
	first_player_raised_bet := NO ||
	bet_value_player_one := 0 ||
	bet_value_player_two := 0 ||
	actual_bet := 5 ||
	first_round := YES ||
	first_player_money := 40 ||
	second_player_money := 40
	
OPERATIONS

  first_gamble =
  PRE first_round = YES & gambleTime = YES & card(playersInGame) = 2
  THEN
  	pool := pool + actual_bet ||
  	IF playerOneTurn = YES
  	THEN
		first_player_money := first_player_money - actual_bet ||
		bet_value_player_one := bet_value_player_one + actual_bet ||
    		playerOneTurn := NO
	ELSE
		second_player_money := second_player_money - actual_bet ||
		bet_value_player_two := bet_value_player_two + actual_bet ||
	    	playerOneTurn := YES
	END ||
	first_round := NO
  END;

  cover_bet =
  PRE first_round = NO & gambleTime = YES & card(playersInGame) = 2
  THEN
    IF playerOneTurn = YES
    THEN
        pool := pool + bet_value_player_two - bet_value_player_one ||
        first_player_money := first_player_money - bet_value_player_two - bet_value_player_one ||
        bet_value_player_one := bet_value_player_two ||
        playerOneTurn := NO
    ELSE
        pool := pool + bet_value_player_one - bet_value_player_two ||
        first_player_money := first_player_money - bet_value_player_one - bet_value_player_two ||
        bet_value_player_two := bet_value_player_one ||
        playerOneTurn := YES
    END ||
    gambleTime := NO ||
    first_round := NO
  END;

  player_raise_bet = 
  PRE gambleTime = YES & card(playersInGame) > 1 & first_round = NO
  THEN
  	actual_bet := actual_bet + 5 ||
  	IF playerOneTurn = YES
  	THEN
		first_player_money := first_player_money - actual_bet ||
  		first_player_raised_bet := YES ||
		bet_value_player_one := bet_value_player_one + actual_bet ||
	    	playerOneTurn := NO
	ELSE
		second_player_money := second_player_money - actual_bet ||
  		first_player_raised_bet := NO ||
		bet_value_player_two := bet_value_player_two + actual_bet ||
	    	playerOneTurn := YES
	END
  END;

  player_quit_game =
  PRE gambleTime = YES & {P_ONE} <: playersInGame
  THEN
	IF playerOneTurn = YES
	THEN 
		playersInGame := playersInGame - {P_ONE} ||
		playerOneTurn := NO ||
		gambleTime := NO
	ELSE
		playersInGame := playersInGame - {P_TWO} ||
		playerOneTurn := YES ||
		gambleTime := NO
	END
  END

END
