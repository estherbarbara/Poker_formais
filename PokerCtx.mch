/* PokerCtx
 * Author: Esther
 */
MACHINE PokerCtx  
SETS
    BOOLEAN = {YES, NO};
    INGAME = {P_ONE, P_TWO, P_NONE}

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
