/* Poker
 * Author: Esther
 */
MACHINE Poker
EXTENDS Dealer

OPERATIONS

	start_gambling = first_gamble;
	continue_gambling = cover_bet;
	upper_gambling = player_raise_bet;
	quit_gambling = player_quit_game;

	first_round_of_cards = deal_comunity_cards;
	second_round_of_cards = deal_two_cards_to_two_players;
	third_and_last_round_of_cards = deal_one_comunity_card

END