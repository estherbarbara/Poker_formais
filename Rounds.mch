/* Rounds
 * Author: Esther
 */
MACHINE
    Rounds

INCLUDES PokerCtx

VARIABLES
    gambleTime, gameFinished

INVARIANT
    gambleTime : BOOLEAN
    & gameFinished : BOOLEAN

INITIALISATION 
	gambleTime := YES ||
	gameFinished := NO

OPERATIONS
	stopGambleTime = 
	PRE 
		gambleTime=YES & gameFinished=NO
	THEN
		gambleTime:=NO
	END;

	startGambleTime = 
	PRE 
		gambleTime=NO & gameFinished=NO
	THEN
		gambleTime:=YES
	END;
	
	finishGame = 
	PRE 
		gameFinished=NO
	THEN
		gameFinished:=YES
	END

END
