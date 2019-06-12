/* PokerCtx
 * Author: Esther
 */
MACHINE PokerCtx  
SETS
    BOOLEAN = {YES, NO};
    INGAME = {P_ONE, P_TWO, P_NONE}

VARIABLES
    gambleTime

INVARIANT
    gambleTime : BOOLEAN

INITIALISATION 
	gambleTime := YES

OPERATIONS
	stopGambleTime = 
	PRE 
		gambleTime=YES
	THEN
		gambleTime:=NO
	END;

	startGambleTime = 
	PRE 
		gambleTime=NO
	THEN
		gambleTime:=YES
	END

END
