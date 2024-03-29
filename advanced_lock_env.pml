/*
	Lock system template model for Assignment 2 of 2IX20 - Software Specification.
	Set up for one lock and a configurable number of ships.

	This file contains:
	- process types for locks and ships that can be used as-is for the single lock case
	- a dummy specification of the main controller
	- initialization for the single-lock, single-ship case.
*/

// LTL formulas to be verified
// Formula p1 holds if the first ship can always eventually enter the lock when going from west to east.
ltl p1 { []<> (ship_status[0] == go_west_to_east_in_lock) }
// The eastern pair of doors and the western pair of doors are never simultaneously open.
ltl p2 { [] (((doors_status.west == open) -> (doors_status.east == closed)) && ((doors_status.east == open) -> (doors_status.west == closed))) }
// //When the lower pair of doors is open, the higher valve is closed.
ltl p3 { [] (((LOCK_ORIENTATION == west_low && doors_status.west == open) -> valve_status.higher == closed ) && ((LOCK_ORIENTATION == east_low && doors_status.east == open) -> valve_status.higher == closed))}
// //When the higher pair of doors is open, the lower valve is closed.
ltl p4 { [] (((LOCK_ORIENTATION == west_low && doors_status.east == open) -> valve_status.lower == closed) && ((LOCK_ORIENTATION == east_low && doors_status.west == open) -> valve_status.lower == closed))}
// //The lower pair of doors is only open when the water level in the lock is low.
ltl p5 { [] (((lock_water_level == low_level) <-> (LOCK_ORIENTATION == west_low && doors_status.west == open)) && ((lock_water_level == low_level) <-> (LOCK_ORIENTATION == east_low && doors_status.east == open)))}
// //The higher pair of doors is only open when the water level in the lock is high.
ltl p6 { [] (((lock_water_level == high_level) <-> (LOCK_ORIENTATION == west_low && doors_status.east == open)) && ((lock_water_level == high_level) <-> (LOCK_ORIENTATION == east_low && doors_status.west == open)))}
// //Always if a ship requests the western pair of doors to open and its status is go_west_to_east, the ship will eventually be inside the lock.
//ltl p7 { [] ((request_west?true && ship_status[0] == go_west_to_east) -> <>(ship_status[0] == go_west_to_east_in_lock))}
// //Always if a ship requests the eastern pair of doors to open and its status is go_east_to_west, the ship will eventually be inside the lock.
// ltl p8 { [] ((request_east?true && ship_status == go_east_to_west) -> <>(ship_status == go_east_to_west_in_lock))}

// The number of locks.
#define N   1
// The number of ships.
#define M   1
// The maximum number of ships immediately at either side of a lock.
#define MAX 2

// Type for direction of ship.
mtype:direction = { go_west_to_east, go_west_to_east_in_lock, go_east_to_west, go_east_to_west_in_lock, goal_reached };

// Type for orientation of lock: side of lock with low water level
mtype:lock_orientation = { west_low, east_low };

// Type for water level.
mtype:level = { low_level, high_level };

// Type for lock side indication.
mtype:side = { west_side, east_side };

// Type for valve side indication.
mtype:valve_side = { low_side, high_side };

// Type for door and valve position.
mtype:pos = { closed, open };

// Datatype to store the status of the doors of a lock.
typedef doorpairs_t {
	mtype:pos west;
	mtype:pos east;
}

// Datatype to store the status of the valves of a lock.
typedef valves_t {
	mtype:pos lower;
	mtype:pos higher;
}

// Orientation of locks
// Needs to be adapted for multiple locks
mtype:lock_orientation LOCK_ORIENTATION = west_low;

// Asynchronous channels to handle ship requests.
chan request_west = [M] of { bool };
chan request_east = [M] of { bool };
// Synchronous channels to indicate that a ship has seen that a particular pair
// of doors has opened.
chan observed_west[N] = [0] of { bool };
chan observed_east[N] = [0] of { bool };

// Status of the water level inside a lock.
mtype:level lock_water_level;
// Is there a ship currently in the lock?
bool lock_is_occupied;

// Status of the ships.
mtype:direction ship_status[M];
// Position of the ships.
byte ship_pos[M];
// Number of ships per position.
byte nr_of_ships_at_pos[N+1];

// Status and synchronous channels for doors and valves.
doorpairs_t doors_status;
valves_t valve_status;
chan change_doors_pos = [0] of { mtype:side };
chan doors_pos_changed = [0] of { bool };
chan change_valve_pos = [0] of { mtype:valve_side };
chan valve_pos_changed = [0] of { bool };

// Lock process type. It reacts to requests to open its doors and valves.
proctype lock(byte lockid) {
	do
	:: change_doors_pos?west_side ->
		if
		:: doors_status.west == closed ->
			doors_status.west = open;
			if
			:: LOCK_ORIENTATION == west_low -> lock_water_level = low_level; // Water flows out through western (low) door
			:: LOCK_ORIENTATION == east_low && doors_status.east == closed && valve_status.lower == closed ->
				lock_water_level = high_level; // Water flows in through western (high) door
			:: else -> skip;
			fi;
		:: doors_status.west == open -> doors_status.west = closed;
		fi;
		doors_pos_changed!true;
	:: change_doors_pos?east_side ->
		if
		:: doors_status.east == closed ->
			doors_status.east = open;
			if
			:: LOCK_ORIENTATION == east_low -> lock_water_level = low_level; // Water flows out through eastern (low) door
			:: LOCK_ORIENTATION == west_low && doors_status.west == closed && valve_status.lower == closed ->
				lock_water_level = high_level; // Water flows in through eastern (high) door
			:: else -> skip;
			fi;
		:: doors_status.east == open -> doors_status.east = closed;
		fi;
		doors_pos_changed!true;
	:: change_valve_pos?low_side ->
		if
		:: valve_status.lower == closed -> valve_status.lower = open;
			lock_water_level = low_level;
		:: valve_status.lower == open -> valve_status.lower = closed;
		fi;
		valve_pos_changed!true;
	:: change_valve_pos?high_side ->
		if
		:: valve_status.higher == closed -> valve_status.higher = open;
			if
			:: LOCK_ORIENTATION == west_low && doors_status.west == closed && valve_status.lower == closed ->
				lock_water_level = high_level; // Water flows in as western (low) door is closed
			:: LOCK_ORIENTATION == east_low && doors_status.east == closed && valve_status.lower == closed ->
				lock_water_level = high_level; // Water flows in as eastern (low) door is closed
			:: else -> skip;
			fi;
		:: valve_status.higher == open -> valve_status.higher = closed;
		fi;
		valve_pos_changed!true;
	od;
}

// Ship process type. Based on its direction and position, it makes requests to open doors,
// and moves when possible.
proctype ship(byte shipid) {
	do
	:: ship_status[shipid] == go_east_to_west && ship_pos[shipid] != 0 ->
		do
		:: doors_status.east == closed ->
			request_east!true;
			atomic { doors_status.east == open ->
				if
				:: !lock_is_occupied ->
						ship_status[shipid] = go_east_to_west_in_lock;
						lock_is_occupied = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_east[0]!true;
						break;
				:: lock_is_occupied ->
						observed_east[0]!true;
				fi; }
		:: atomic { doors_status.east == open &&
			!lock_is_occupied ->
				ship_status[shipid] = go_east_to_west_in_lock;
				lock_is_occupied = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	:: ship_status[shipid] == go_east_to_west_in_lock ->
		do
		:: doors_status.west == closed ->
			request_west!true;
			atomic { doors_status.west == open ->
				if
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
					|| ship_pos[shipid]-1 == 0) ->
						ship_status[shipid] = go_east_to_west;
						lock_is_occupied = false;
						ship_pos[shipid]--;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_west[0]!true;
						break;
				:: (nr_of_ships_at_pos[ship_pos[shipid]-1] == MAX
					&& ship_pos[shipid]-1 != 0) ->
						observed_west[0]!true;
				fi; }
		:: atomic { doors_status.west == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]-1] < MAX
			|| ship_pos[shipid]-1 == 0) ->
				ship_status[shipid] = go_east_to_west;
				lock_is_occupied = false;
				ship_pos[shipid]--;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	:: ship_status[shipid] == go_west_to_east && ship_pos[shipid] != N ->
		do
		:: doors_status.west == closed ->
			request_west!true;
			atomic { doors_status.west == open ->
				if
				:: !lock_is_occupied ->
						ship_status[shipid] = go_west_to_east_in_lock;
						lock_is_occupied = true;
						nr_of_ships_at_pos[ship_pos[shipid]]--;
						observed_west[0]!true;
						break;
				:: lock_is_occupied ->
						observed_west[0]!true;
				fi; }
		:: atomic { doors_status.west == open &&
			!lock_is_occupied ->
				ship_status[shipid] = go_west_to_east_in_lock;
				lock_is_occupied = true;
				nr_of_ships_at_pos[ship_pos[shipid]]--;
				break; }
		od;
	:: ship_status[shipid] == go_west_to_east_in_lock ->
		do
		:: doors_status.east == closed ->
			request_east!true;
			atomic { doors_status.east == open ->
				if
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
					|| ship_pos[shipid]+1 == N) ->
						ship_status[shipid] = go_west_to_east;
						lock_is_occupied = false;
						ship_pos[shipid]++;
						nr_of_ships_at_pos[ship_pos[shipid]]++;
						observed_east[0]!true;
						break;
				:: (nr_of_ships_at_pos[ship_pos[shipid]+1] == MAX
					&& ship_pos[shipid]+1 != N) ->
						observed_east[0]!true;
				fi; }
		:: atomic { doors_status.east == open &&
			(nr_of_ships_at_pos[ship_pos[shipid]+1] < MAX
			|| ship_pos[shipid]+1 == N) ->
				ship_status[shipid] = go_west_to_east;
				lock_is_occupied = false;
				ship_pos[shipid]++;
				nr_of_ships_at_pos[ship_pos[shipid]]++;
				break; }
		od;
	:: ship_status[shipid] == go_east_to_west && ship_pos[shipid] == 0 ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_west_to_east;
	:: ship_status[shipid] == go_west_to_east && ship_pos[shipid] == N ->
		ship_status[shipid] = goal_reached; ship_status[shipid] = go_east_to_west;
	od;
}

// DUMMY main control process type. Remodel it to control the lock system and handle
// requests of ships!
proctype main_control() {
	do
	:: request_west?true ->
		if 
		:: LOCK_ORIENTATION == west_low && doors_status.west == closed ->
			if 
			:: valve_status.higher == open ->
				change_valve_pos!high_side; valve_pos_changed?true;
			:: valve_status.higher == closed -> skip;
			fi;
			if
			:: lock_water_level == high_level ->
				if 
				:: valve_status.lower == closed ->
					change_valve_pos!low_side; valve_pos_changed?true;
				:: else -> skip;
				fi;
			:: lock_water_level == low_level && valve_status.lower == open ->
				change_valve_pos!low_side; valve_pos_changed?true;
			fi;
			change_doors_pos!west_side; doors_pos_changed?true;
		:: LOCK_ORIENTATION == east_low && doors_status.west == closed ->
			if 
			:: valve_status.lower == open ->
				change_valve_pos!low_side; valve_pos_changed?true;
			:: valve_status.lower == closed -> skip;
			fi;
			if
			:: lock_water_level == low_level ->
				if 
				:: valve_status.higher == closed ->
					change_valve_pos!high_side; valve_pos_changed?true;
				:: else -> skip;
				fi;
			:: lock_water_level == high_level && valve_status.higher == open ->
				change_valve_pos!high_side; valve_pos_changed?true;
			fi;
			change_doors_pos!west_side; doors_pos_changed?true;
		:: doors_status.west == open -> skip;
		fi;
		observed_west[0]?true;
		if 
		:: doors_status.west == open ->
			change_doors_pos!west_side; doors_pos_changed?true;
		:: doors_status.west == closed -> skip;
		fi;
		// if
		// :: doors_status.west == closed ->
		// 	change_doors_pos!west_side; doors_pos_changed?true;
		// :: doors_status.west == open -> skip;
		// fi;
		// observed_west[0]?true;
	:: request_east?true ->
		if 
		:: LOCK_ORIENTATION == east_low && doors_status.east == closed ->
			if 
			:: valve_status.higher == open ->
				change_valve_pos!high_side; valve_pos_changed?true;
			:: valve_status.higher == closed -> skip;
			fi;
			if
			:: lock_water_level == high_level ->
				if 
				:: valve_status.lower == closed ->
					change_valve_pos!low_side; valve_pos_changed?true;
				:: else -> skip;
				fi;
			:: lock_water_level == low_level && valve_status.lower == open ->
				change_valve_pos!low_side; valve_pos_changed?true;
			fi;
			change_doors_pos!east_side; doors_pos_changed?true;
		:: LOCK_ORIENTATION == west_low && doors_status.east == closed ->
			if 
			:: valve_status.lower == open ->
				change_valve_pos!low_side; valve_pos_changed?true;
			:: valve_status.lower == closed -> skip;
			fi;
			if
			:: lock_water_level == low_level ->
				if 
				:: valve_status.higher == closed ->
					change_valve_pos!high_side; valve_pos_changed?true;
				:: else -> skip;
				fi;
			:: lock_water_level == high_level && valve_status.higher == open ->
				change_valve_pos!high_side; valve_pos_changed?true;
			fi;
			change_doors_pos!east_side; doors_pos_changed?true;
		:: doors_status.east == open -> skip;
		fi;
		observed_east[0]?true;
		if 
		:: doors_status.east == open ->
			change_doors_pos!east_side; doors_pos_changed?true;
		:: doors_status.east == closed -> skip;
		fi;
		// if
		// :: doors_status.east == closed ->
		// 	change_doors_pos!east_side; doors_pos_changed?true;
		// :: doors_status.east == open -> skip;
		// fi;
		// observed_east[0]?true;
	od;
}

proctype monitor() {
	// an example assertion.
	assert(0 <= ship_pos[0] && ship_pos[0] <= N);
}

// Initial process that instantiates all other processes and creates
// the initial lock and ship situation.
init {
	byte proc;
	atomic {
		//run monitor();
		run main_control();
		// In the code below, the individual locks are initialised.
		// The assumption here is that N == 1. When generalising the model for
		// multiple locks, make sure that the do-statement is altered!
		proc = 0;
		do
		:: proc < N ->
			doors_status.west = closed;
			doors_status.east = closed;
			valve_status.lower = closed;
			valve_status.higher = closed;
			lock_water_level = high_level;
			lock_is_occupied = false;
			run lock(proc);
			proc++;
		:: proc == N -> break;
		od;
		// In the code below, the individual ship positions and directions
		// are initialised. Expand this when more ships should be added.
		proc = 0;
		do
		:: proc == 0 -> ship_status[proc] = go_west_to_east; ship_pos[proc] = 0;
			run ship(proc); proc++;
		:: proc > 0 && proc < M -> proc++;
		:: proc == M -> break;
		od;
		// Do not change the code below! It derives the number of ships per
		// position from the positions of the individual ships.
		proc = 0;
		do
		:: proc < M -> nr_of_ships_at_pos[ship_pos[proc]]++; proc++;
		:: else -> break;
		od;
	}
}s