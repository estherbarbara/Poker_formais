/* Gambler
 * Author: Esther
 */
MACHINE Gambler  
EXTENDS Rounds

VARIABLES 
    playerOneTurn, playersInGame, 
    pool, first_player_raised_bet, bet_value_player_one, bet_value_player_two, actual_bet, first_round,
    first_player_money, second_player_money
    
INVARIANT
    playerOneTurn : BOOLEAN
    & first_round : BOOLEAN
    & playersInGame <: INGAME
    & pool : NAT
    & first_player_raised_bet : BOOLEAN
    & bet_value_player_one : NAT
    & bet_value_player_two : NAT
    & actual_bet : NAT
    & first_player_money : INT
    & second_player_money : INT
    & pool = bet_value_player_one + bet_value_player_two 
    & first_player_money + bet_value_player_one + second_player_money + bet_value_player_two = 200


INITIALISATION 
	playerOneTurn := YES ||
	playersInGame := {P_ONE, P_TWO} ||
	pool := 0 ||
	first_player_raised_bet := NO ||
	bet_value_player_one := 0 ||
	bet_value_player_two := 0 ||
	actual_bet := 5 ||
	first_round := YES ||
	first_player_money := 100 ||
	second_player_money := 100
	
OPERATIONS

  total, left_one, left_two <-- first_gamble =
  PRE first_round = YES & gambleTime = YES & gameFinished = NO &  card(playersInGame) > 1
  THEN
  	pool := pool + actual_bet ||
  	total := pool + actual_bet ||
  	IF playerOneTurn = YES
  	THEN
		    first_player_money := first_player_money - actual_bet ||
		    left_one := first_player_money - actual_bet ||
		    left_two := second_player_money ||
		    bet_value_player_one := bet_value_player_one + actual_bet ||
    		playerOneTurn := NO
	  ELSE
		    second_player_money := second_player_money - actual_bet ||
		    left_two := second_player_money - actual_bet ||
		    left_one := first_player_money ||
		    bet_value_player_two := bet_value_player_two + actual_bet ||
	    	playerOneTurn := YES
	END ||
	first_round := NO
  END;

  total, left_one, left_two <-- cover_bet =
  PRE first_round = NO & gambleTime = YES & gameFinished = NO &  card(playersInGame) > 1
  THEN
    IF playerOneTurn = YES
    THEN
        pool := pool + bet_value_player_two - bet_value_player_one ||
        total := pool + bet_value_player_two - bet_value_player_one ||
        first_player_money := first_player_money -  (bet_value_player_two - bet_value_player_one) ||
        left_two := second_player_money ||
        left_one := first_player_money -  (bet_value_player_two - bet_value_player_one) ||
        bet_value_player_one := bet_value_player_one + (bet_value_player_two - bet_value_player_one) ||
        playerOneTurn := NO
    ELSE
        pool := pool + bet_value_player_one - bet_value_player_two ||
        total := pool + bet_value_player_one - bet_value_player_two ||
        second_player_money := second_player_money - (bet_value_player_one - bet_value_player_two) ||
        left_one := first_player_money ||
        left_two := second_player_money - (bet_value_player_one - bet_value_player_two) ||
        bet_value_player_two := bet_value_player_two + (bet_value_player_one - bet_value_player_two) ||
        playerOneTurn := YES
    END ||
    stopGambleTime ||
    first_round := YES

  END;

  total, left_one, left_two <-- player_raise_bet = 
  PRE first_round = NO & gambleTime = YES & gameFinished = NO  & card(playersInGame) > 1
  THEN
  	actual_bet := actual_bet + 5 ||
  	pool := pool + actual_bet + 5 ||
  	total := pool + actual_bet + 5 ||
  	IF playerOneTurn = YES
  	THEN
		first_player_money := first_player_money - (actual_bet +5) ||
  		first_player_raised_bet := YES ||
		bet_value_player_one := bet_value_player_one + actual_bet + 5 ||
		left_one := first_player_money - (actual_bet +5) ||
		left_two := second_player_money ||
	    playerOneTurn := NO
	ELSE
		second_player_money := second_player_money - (actual_bet + 5) ||
  		first_player_raised_bet := NO ||
		bet_value_player_two := bet_value_player_two + actual_bet + 5 ||
		left_one := second_player_money - (actual_bet +5) ||
		left_two := first_player_money ||
	    playerOneTurn := YES
	END
  END;

  total, left_one, left_two <-- player_quit_game =
  PRE gambleTime = YES & gameFinished = NO & card(playersInGame) > 1
  THEN
	IF playerOneTurn = YES
	THEN 
		second_player_money := second_player_money + pool ||
		left_one := first_player_money ||
		left_two := second_player_money + pool ||
		
		bet_value_player_one := 0 ||
		bet_value_player_two := 0 ||
		pool := 0 ||
		playersInGame := playersInGame - {P_ONE} ||
		playerOneTurn := NO ||
		finishGame
	ELSE
		first_player_money := first_player_money + pool ||
		left_one := first_player_money + pool ||
		left_two := second_player_money ||
		
		bet_value_player_one := 0 ||
		bet_value_player_two := 0 ||
		pool := 0 ||
		playersInGame := playersInGame - {P_TWO} ||
		playerOneTurn := YES ||
		finishGame
	END ||
	total := 0 ||
    first_round := YES
  END;
  
  total, left_one, left_two <-- player_one_win_game =
  PRE gameFinished = NO & card(playersInGame) > 1 & {P_ONE} <: playersInGame
  THEN
		playersInGame := playersInGame - {P_ONE} ||
		first_player_money := first_player_money + pool ||
		bet_value_player_one := 0 ||
		bet_value_player_two := 0 ||
		playerOneTurn := NO ||
		pool := 0 ||
		finishGame ||
		first_round := YES ||
		total := 0 ||
		left_one := first_player_money + pool ||
		left_two := second_player_money
		
  END;
  
  total, left_one, left_two <-- player_two_win_game =
  PRE gameFinished = NO & card(playersInGame) > 1 & {P_TWO} <: playersInGame
  THEN
		playersInGame := playersInGame - {P_ONE} ||
		second_player_money := second_player_money + pool ||
		bet_value_player_one := 0 ||
		bet_value_player_two := 0 ||
		playerOneTurn := NO ||
		pool := 0 ||
		finishGame ||
		first_round := YES ||
		total := 0 ||
		left_one := first_player_money ||
		left_two := second_player_money + pool
		
  END

END
