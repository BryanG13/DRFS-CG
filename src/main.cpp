/*
 * Demand Responsive Feeder Service - Column Generation (DRFS-CG)
 * 
 * This program solves a bus routing optimization problem using Column Generation.
 * It assigns passengers to buses and determines optimal routes considering:
 * - Travel time (bus routing)
 * - Walking time (passenger to station)
 * - Waiting time (passenger arrival vs bus arrival)
 */

// CPLEX optimization library
#include <ilcplex/ilocplex.h>

#include <iostream>
#include <stdlib.h> 
#include <math.h>
#include <list>

using namespace std;

// ============================================================================
// UTILITY FUNCTIONS - QuickSort for sorting passengers by arrival time
// ============================================================================

/**
 * Partition function for QuickSort algorithm
 * Sorts both index and distance arrays simultaneously
 * @param index[] - Array of indices to be sorted
 * @param dist[] - Array of distances (sorting key)
 * @param low - Starting index
 * @param high - Ending index
 * @return Partition index
 */
int partition(int index[], double dist[], int low, int high) {
	double pivot = dist[high]; // Choose last element as pivot
	int i = (low - 1); // Index of smaller element

	// Iterate through array and partition around pivot
	for (int j = low; j <= high - 1; j++) {
		if (dist[j] < pivot) {
			i++; // Increment index of smaller element
			
			// Swap indices
			double t = index[j];
			index[j] = index[i];
			index[i] = t;

			// Swap distances
			double t0 = dist[j];
			dist[j] = dist[i];
			dist[i] = t0;
		}
	}
	// Place pivot in correct position
	double t = index[high];
	index[high] = index[i + 1];
	index[i + 1] = t;

	double t0 = dist[high];
	dist[high] = dist[i + 1];
	dist[i + 1] = t0;

	return (i + 1);
}

/**
 * QuickSort main function
 * Recursively sorts arrays by partitioning
 * @param index[] - Array of indices to be sorted
 * @param dist[] - Array of distances (sorting key)
 * @param low - Starting index
 * @param high - Ending index
 */
void quickSort(int index[], double dist[], int low, int high) {
	if (low < high) {
		// Find partition index - element is now in correct position
		int pi = partition(index, dist, low, high);

		// Recursively sort elements before and after partition
		quickSort(index, dist, low, pi - 1);
		quickSort(index, dist, pi + 1, high);
	}
}

// ============================================================================
// CPLEX CALLBACK - Subtour Elimination
// ============================================================================

/**
 * Lazy Constraint Callback for Subtour Elimination
 * This callback is invoked by CPLEX when an integer solution is found.
 * It checks for subtours in the routing solution and adds constraints to eliminate them.
 * 
 * @param y - Binary routing variables (y[i][j] = 1 if arc from station i to j is used)
 * @param Stations - Total number of stations
 * @param N - Number of mandatory stations
 * @param C - Number of customers/passengers
 */
ILOSTLBEGIN
ILOLAZYCONSTRAINTCALLBACK4(SubtourEliminationCallback, IloArray<IloBoolVarArray>, y, int, Stations, int, N, int, C) {
	int i, j, k, p, n;
	vector<int> sta;

	// Build list of stations that are visited (have outgoing arcs)
	n = N;
	sta.clear();
	
	// Add all mandatory stations (except first one)
	for (j = 1; j < N; j++) sta.push_back(j);
	
	// Add optional stations that are actually visited
	for (j = N; j < Stations; j++) {
		for (p = 0; p < Stations; p++) {
			// Check if this optional station has an outgoing arc
			if (((int)getValue(y[j][p] + 0.001) == 1)) {
				sta.push_back(j);
				n++;
				break;
			}
		}
	}

	// Initialize arrays for subtour detection
	bool* seen = new bool[Stations];      // Track which stations have been visited
	int* visited = new int[n + 1];        // Store the order of visited stations

	memset(seen, false, sizeof(bool) * Stations);
	memset(visited, 0, sizeof(int) * n + 1);
	int length = 0;
	k = 0;
	seen[0] = true;  // Start from depot (station 0)

	// Trace through the route to detect subtours
	while (true) {
		// Find next station in the route
		for (j = 0; j < Stations; j++) {
			if (k != j) {
				// Check if there's an arc from k to j
				if (((int)getValue(y[k][j] + 0.001) == 1)) {
					visited[++length] = j;
					
					// If we've seen this station before, we found a subtour
					if (seen[j]) {
						break;
					}
					
					seen[j] = true;
					k = j;
					j = -1;  // Reset to search from beginning

					// Remove this station from unvisited list
					for (p = 0; p < sta.size(); p++) {
						if (sta[p] == k) {
							sta.erase(sta.begin() + p);
							break;
						}
					}
				}
			}
		}
		
		// Check termination conditions
		if (length < n - 1 && visited[0] != visited[length]) {
			// Incomplete tour - start from another unvisited station
			if (n == N && length >= N - 1) break;
			k = sta[0];
			length = 0;
			memset(seen, false, sizeof(bool) * Stations);
			memset(visited, 0, sizeof(int) * n + 1);
			visited[length] = k;
			seen[k] = true;
		}
		else if (length < n && length > 0 || sta.size() == 0) {
			// Found a subtour or visited all stations
			break;
		}
		else if (length == 0) {
			// No arc found from current station, try next one
			if (k < n - 1) k++;
			else {
				length = n;
				break;
			}
			length = 0;
			memset(seen, false, sizeof(bool) * Stations);
			memset(visited, 0, sizeof(int) * n + 1);
			visited[length] = k;
			seen[k] = true;
		}
	}
	
	int l0 = length;
	
	// If we found a subtour (not a complete tour), add constraint to eliminate it
	if (length > 0 && length < n - 1) {
		length = l0;
		IloExpr clique(getEnv());
		int firstjobinloop = visited[length];
		int newlen = 0;
		
		// Build constraint: sum of arcs in subtour <= (number of nodes in subtour - 1)
		// This forces the subtour to be broken
		while (true) {
			j = visited[length];
			k = visited[--length];
			clique += y[k][j];
			newlen++;
			if (k == firstjobinloop) break;
		}
		
		// Add the subtour elimination constraint
		add(clique <= newlen - 1).end();
		clique.end();
	}
	
	delete[] seen;
	delete[] visited;

	return;
}

// ============================================================================
// MAIN PROGRAM
// ============================================================================

int main() {

	int i, j, k, p, c, l;

	// ========================================================================
	// WEIGHT FACTORS - For multi-objective cost function
	// ========================================================================
	float c1 = 0.25f;  // Weight for travel/dwell time
	float c2 = 0.35f;  // Weight for walking time
	float c3 = 1 - c1 - c2;  // Weight for waiting time (0.40)
	float lvsea = 1;   // Penalty multiplier for late arrivals vs early arrivals

	int instance = -1;
	//Define parameters-----------------------------------------------------------------------
	const int nBuses = 2; // number of buses available
	const int N = 5; // number of mandatory stations
	const int M = 3; // number of stations in cluster
	const int Stations = (N - 1) * M + N; // amount of Stations
	const int C = 15; // amount of clients in opt horizon
	const float pspeed = 1.0f; // passengers speed in meter per scond
	const float bspeed = 40.0f / 3.6f; //bus speed in m/s
	const int delta = 30; // acceleration and deceleration time  in seconds
	const int tau = 5; //dwell time coeficient in seconds
	const int d = 20 * 60; // threshold of individual walking time in sec
	const int d_time1 = 15 * 60; // Maximum amount of time a passenger can arrive too early
	const int d_time2 = 5 * 60; // Maximum amount of time a passenger can arrive too late 
	const int bCapacity = 15; // Bus capcity

	int estbus;
	if (C % nBuses == 0) estbus = C / nBuses;
	else estbus = C / nBuses + 1;

	// Read passenger locations (x, y coordinates)
	double passengers[C][2];
	ifstream filep("data/input/passengers.txt");
	i = 0;
	while (i < C) {
		filep >> passengers[i][0] >> passengers[i][1];
		i++;
	}

	// Read mandatory station locations
	double mandatory[N][2];
	ifstream filem("data/input/mandatory.txt");
	i = 0;
	while (i < N) {
		filem >> mandatory[i][0] >> mandatory[i][1];
		i++;
	}

	// Read optional station locations
	double optional[(N - 1) * M][2];
	ifstream fileo("data/input/optional.txt");
	i = 0;
	while (i < (N - 1) * M) {
		fileo >> optional[i][0] >> optional[i][1];
		i++;
	}

	// Read desired arrival times of passengers
	double arrivals[C];
	ifstream filea("data/input/arrivals.txt");
	i = 0;
	while (i < C) {
		filea >> arrivals[i];
		i++;
	}

	// ========================================================================
	// CALCULATE TRAVEL TIMES using Manhattan distance
	// ========================================================================
	double traveltimep[C][Stations];        // Walking time: passenger to station
	double traveltimes[Stations][Stations]; // Bus travel time: station to station

	// Calculate walking times from passengers to all stations
	for (int i = 0; i < C; i++) {
		// To mandatory stations
		for (int j = 0; j < N; j++) {
			traveltimep[i][j] = (abs(passengers[i][0] - mandatory[j][0]) + 
			                     abs(passengers[i][1] - mandatory[j][1])) * 1000 / pspeed;
		}
		// To optional stations
		for (int j = N; j < Stations; j++) {
			traveltimep[i][j] = (abs(passengers[i][0] - optional[j - N][0]) + 
			                     abs(passengers[i][1] - optional[j - N][1])) * 1000 / pspeed;
		}
	}

	// Calculate bus travel times between all stations
	// Mandatory to mandatory and mandatory to optional
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < N; j++) {
			traveltimes[i][j] = (abs(mandatory[i][0] - mandatory[j][0]) + 
			                     abs(mandatory[i][1] - mandatory[j][1])) * 1000 / bspeed;
		}
		for (int j = N; j < Stations; j++) {
			traveltimes[i][j] = (abs(mandatory[i][0] - optional[j - N][0]) + 
			                     abs(mandatory[i][1] - optional[j - N][1])) * 1000 / bspeed;
		}
	}

	// Optional to mandatory and optional to optional
	for (int i = N; i < Stations; i++) {
		for (int j = 0; j < N; j++) {
			traveltimes[i][j] = (abs(optional[i - N][0] - mandatory[j][0]) + 
			                     abs(optional[i - N][1] - mandatory[j][1])) * 1000 / bspeed;
		}
		for (int j = N; j < Stations; j++) {
			traveltimes[i][j] = (abs(optional[i - N][0] - optional[j - N][0]) + 
			                     abs(optional[i - N][1] - optional[j - N][1])) * 1000 / bspeed;
		}
	}

	// ========================================================================
	// DEFINE INDEX SETS
	// ========================================================================
	int I[nBuses];     // Set of buses
	int J[Stations];   // Set of all stations
	int F[N];          // Set of mandatory (fixed) stations
	int O[(N - 1) * M]; // Set of optional stations
	int P[C];          // Set of passengers
	
	for (int i = 0; i < nBuses; i++) {
		I[i] = i;
	}
	for (int i = 0; i < Stations; i++) {
		J[i] = i;
	}
	for (int i = 0; i < N; i++) {
		F[i] = i;
	}
	for (int i = N; i < Stations; i++) {
		O[i - N] = i;
	}
	for (int i = 0; i < C; i++) {
		P[i] = i;
	}

	// ========================================================================
	// PRE-PROCESSING - Sort passengers by arrival time
	// ========================================================================
	int indexpt[C];
	double temparrivals[C];

	for (p = 0; p < C; p++) {
		indexpt[p] = p;
		temparrivals[p] = arrivals[p];
	}
	
	// Sort passengers by arrival time for better initial solution
	quickSort(indexpt, temparrivals, 0, C - 1);

	// ========================================================================
	// INITIALIZATION - Construct initial feasible solution using greedy heuristic
	// ========================================================================
	double cost = 0;

	// Initial solution variables
	bool xk0[nBuses][C][Stations];         // Passenger-to-station assignments
	bool yk0[nBuses][Stations][Stations];  // Bus routing (arcs between stations)
	double Ak0[nBuses];                    // Bus arrival times
	double Dk0[nBuses];                    // Bus departure times (delay from depot)

	// Helper variables for constructing initial solution
	int pa = 0, p_new, p_0;
	int cap = 0, countcap = 0;
	int min = INT_MAX;
	int mini = -1;
	int sumx = 0;

	double earliestArr, latestArr, Arr;
	int minps = 10000000;
	int minpsi = 0;
	int imand, firstmin, firstminj;
	bool inSuccessor, inGraph;

	double timewindow;
	double firsttw;

	// Build initial solution for each bus
	for (i = 0; i < nBuses; i++) {
		cap = 0;
		
		// Initialize routing variables (y) to 0
		for (j = 0; j < Stations; j++) {
			for (int k = 0; k < Stations; k++) {
				yk0[i][j][k] = 0;
			}
		}

		// Initialize passenger assignment variables (x) to 0
		for (p = 0; p < C; p++) {
			for (k = 0; k < Stations; k++) {
				xk0[i][p][k] = 0;
			}
		}

		// PHASE 1: Assign passengers to nearest feasible stations
		for (p = pa; p < C; p++) {
			// Calculate time window for passenger grouping
			if (cap > 0) timewindow = abs(firsttw - arrivals[indexpt[p]]);
			else {
				firsttw = arrivals[indexpt[p]];
				timewindow = 0;
			}
			
			// Check if passenger can be added to this bus (capacity and time window constraints)
			if (cap < bCapacity && pa < C && (int)timewindow <= d_time1 + d_time2) {
				// Find nearest station for this passenger
				minps = 10000000;
				minpsi = 0;

				for (int j = 0; j < Stations; j++) {
					if (traveltimep[indexpt[p]][j] < minps) {
						minps = traveltimep[indexpt[p]][j];
						minpsi = j;
					}
				}
				
				// Assign passenger to nearest station if within walking threshold
				if (traveltimep[indexpt[p]][minpsi] <= d) {
					xk0[i][indexpt[p]][minpsi] = 1;
					cap++;
					pa++;
				}
				else {
					std::cout << "INFEASIBLE FOR WALKING \n";
					exit(0);
				}
			}
		}

		// PHASE 2: Construct bus route through assigned stations
		p = 0;
		j = 0;  // Start from depot (station 0)
		imand = 0;

		while (j != N - 1) {  // Continue until reaching last mandatory station
			//cout << j << endl;
			// determine the last mandatory station visited 
			if (j < N - 1) imand = j;

			//cout << j << " Has NO successor  "  ;
			firstmin = 100000000, firstminj = -1;
			for (k = N + imand * M; k < N + (imand + 1) * M; k++) { // first check the optional stations 
				//check if node is in chosen subset
				inGraph = false;
				for (p = 0; p < C; p++) {
					if (xk0[i][p][k] > 0) {
						inGraph = true;
						break;
					}
				}

				//check if node is already a successor
				inSuccessor = false;
				for (l = 0; l < Stations; l++) {
					if (yk0[i][l][k] == 1) {
						inSuccessor = true;
						//cout << "successor 1 is " << k + 1 << endl;
						break;
					}
				}

				//calculate closest eligible stop (it is among the chosen stops and it is not a succeesor yet )
				if (inGraph && j != k && !inSuccessor) {
					//if ( it == 657841 && i == 0)cout << " k is " << k << " and distance is " << traveltimes[j][k] << " and is eligible " << endl;
					if (firstmin > traveltimes[j][k]) {
						firstmin = traveltimes[j][k];
						firstminj = k;
					}
				}
			}
			if (firstminj == -1) { // if there are no elegible optional stations
				//cout << " no optional in same cluster available"<< endl;
				for (k = 1; k < N; k++) { //then check the mandatory ones

					//check if node is already a successor
					inSuccessor = false;
					for (l = 0; l < Stations; l++) {
						if (yk0[i][l][k] == 1) {
							inSuccessor = true;
							//cout << "successor 2 is " << k + 1 << endl;
							break;
						}
					}

					//calculate closest eligible stop (it is among the chosen stops and it is not a succeesor yet )
					if (j != k && !inSuccessor) {
						//cout << " k is " << k << " and distance is " << traveltimes[j][k] << " and is eligible " << endl;
						if (firstmin > traveltimes[j][k]) {
							firstmin = traveltimes[j][k];
							firstminj = k;
							//cout << " k is " << k << endl;
						}
					}
				}

				//if (firstminj == -1) cout << " no mandatory available" << endl;
				//and check the next or previous cluster of optionals
				for (k = std::max(N + (imand - 1) * M, N); k < std::min(N + (imand + 2) * M, Stations); k++) {
					// Check if station has assigned passengers
					inGraph = false;
					for (p = 0; p < C; p++) {
						if (xk0[i][p][k] == 1) {
							inGraph = true;
							break;
						}
					}

					// Check if already a successor
					inSuccessor = false;
					for (l = 0; l < Stations; l++) {
						if (yk0[i][l][k] == 1) {
							inSuccessor = true;
							break;
						}
					}

					// If eligible, consider as candidate
					if (inGraph && j != k && !inSuccessor) {
						if (firstmin > traveltimes[j][k]) {
							firstmin = traveltimes[j][k];
							firstminj = k;
						}
					}
				}
			}
			
			// Add arc to nearest eligible station
			yk0[i][j][firstminj] = 1;
			yk0[i][firstminj][j] = 0; // Prevent reverse arc (avoid loops)
			j = firstminj;  // Move to next station
		}

		// PHASE 3: Calculate bus arrival time at destination
		Ak0[i] = 0;
		// Sum up all travel and dwell times
		for (j = 0; j < Stations; j++) {
			for (k = 0; k < Stations; k++) {
				Ak0[i] += (traveltimes[j][k] + delta) * yk0[i][j][k];
			}
			for (c = 0; c < C; c++) {
				Ak0[i] += (double)tau * xk0[i][c][j];
			}
		}

		// PHASE 4: Determine optimal bus departure time
		if (cap > 0) {
			// Find earliest and latest passenger arrival times on this bus
			earliestArr = 1000000;
			latestArr = -1;
			
			// Find earliest passenger
			for (p = 0; p < C; p++) {
				sumx = 0;
				for (int j = 0; j < Stations; j++) sumx += xk0[i][indexpt[p]][j];
				if (sumx == 1) {
					earliestArr = arrivals[indexpt[p]];
					break;
				}
			}
			
			// Find latest passenger
			for (p = C - 1; p >= 0; p--) {
				sumx = 0;
				for (int j = 0; j < Stations; j++) sumx += xk0[i][indexpt[p]][j];
				if (sumx == 1) {
					latestArr = arrivals[indexpt[p]];
					break;
				}
			}

			// Find arrival time that minimizes total waiting time
			double sum_min = 100000000000000;
			Arr = Ak0[i];
			for (int cc = latestArr - d_time1; cc <= earliestArr + d_time2; cc++) {
				double sum = 0;
				for (c = 0; c < C; c++) {
					sumx = 0;
					for (int j = 0; j < Stations; j++) sumx += xk0[i][c][j];
					if (sumx == 1) {
						sum += abs(arrivals[c] - cc);
					}
				}
				if (sum_min > sum) {
					sum_min = sum;
					Arr = cc;
				}
			}
			Arr = earliestArr + d_time2;  // Use slightly late arrival
		}
		else {
			Arr = Ak0[i];  // No passengers, use travel time
		}

		// Calculate departure delay needed
		Dk0[i] = Arr - Ak0[i];
		Ak0[i] = Arr;
		
		// PHASE 5: Calculate cost of this bus route
		for (j = 0; j < Stations; j++) {
			for (k = 0; k < Stations; k++) {
				cost += c1 * yk0[i][j][k] * (traveltimes[j][k] + delta);
			}

			for (p = 0; p < C; p++) {
				cost += xk0[i][p][j] * (c1 * (double)tau + c2 * traveltimep[p][j]);
			}
		}

		// Add waiting time costs
		for (p = 0; p < C; p++) {
			sumx = 0;
			for (j = 0; j < Stations; j++) sumx += xk0[i][p][j];
			if (sumx == 1) {
				if (arrivals[p] > Ak0[i]) cost += c3 * abs(arrivals[p] - Ak0[i]);
				else cost += lvsea * c3 * abs(arrivals[p] - Ak0[i]);
			}
		}
	}

	// ========================================================================
	// PREPARE FOR COLUMN GENERATION
	// Store initial solution in column pool
	// ========================================================================
	int it;
	int K = nBuses;  // Number of columns (route configurations)

	// Column pool - stores all generated route configurations
	vector<vector<vector<bool>>> xk(K);     // Passenger assignments for each column
	vector<vector<vector<bool>>> yk(K);     // Bus routes for each column
	vector<vector<double>> Ak(K);           // Arrival times for each column
	vector<vector<double>> qk_early(K);     // Early arrival penalties
	vector<vector<double>> qk_late(K);      // Late arrival penalties
	vector<double> Dk(K);                   // Departure times for each column

	// Transfer initial solution to column pool
	for (i = 0; i < K; i++) {
		vector<vector<bool>> xkm(C);
		vector<vector<bool>> ykm(Stations);
		vector<double> Akk(C);
		vector<double> qkk_early(C);
		vector<double> qkk_late(C);

		// Copy routing variables
		for (j = 0; j < Stations; j++) {
			vector<bool> ykr(Stations);
			for (int k = 0; k < Stations; k++) {
				ykr[k] = yk0[i][j][k];
			}
			ykm[j] = ykr;
		}
		yk[i] = ykm;

		// Copy passenger assignment variables
		for (p = 0; p < C; p++) {
			vector<bool> xkr(Stations);
			for (int k = 0; k < Stations; k++) {
				xkr[k] = xk0[i][p][k];
			}
			xkm[p] = xkr;
		}
		xk[i] = xkm;

		// Calculate arrival times and waiting penalties for each passenger
		for (p = 0; p < C; p++) {
			int sumX = 0;
			for (int j = 0; j < Stations; j++) {
				sumX += xk0[i][p][j];
			}

			if (sumX == 1) {  // Passenger assigned to this bus
				Akk[p] = Ak0[i];
				if (Akk[p] >= arrivals[p]) {
					qkk_early[p] = 0;
					qkk_late[p] = Akk[p] - arrivals[p];
					if (qkk_late[p] - d_time2 > 0.001) {
						std::cout << "WRONG too late by: " << (qkk_late[p] - d_time2) / 60 
						          << " minutes on bus " << i + 1 << endl;
					}
				}
				else {
					qkk_early[p] = arrivals[p] - Akk[p];
					qkk_late[p] = 0;
					if (qkk_early[p] - d_time1 > 0.001) {
						std::cout << "WRONG too early by: " << (qkk_early[p] - d_time1) / 60 
						          << " minutes on bus " << i + 1 << endl;
					}
				}
			}
			else {  // Passenger not on this bus
				Akk[p] = arrivals[p];
				qkk_early[p] = 0;
				qkk_late[p] = 0;
			}
		}

		Ak[i] = Akk;
		qk_early[i] = qkk_early;
		qk_late[i] = qkk_late;
		Dk[i] = Dk0[i];
	}

	// ========================================================================
	// COLUMN GENERATION MAIN LOOP
	// ========================================================================
	double elapsed_time = 0;
	clock_t start_time;

	start_time = clock();

	double reducedCost = -10000;  // Initialize to trigger first iteration
	it = 1;
	double sigma = 0;   // Dual variable for bus count constraint
	double pi[C];       // Dual variables for passenger assignment constraints

	// Calculate bounds for arrival time window
	double EA = 10000000000, LA = -1;
	for (int p = 0; p < C; p++) {
		if (EA > arrivals[p]) EA = arrivals[p];
		if (LA < arrivals[p]) LA = arrivals[p];
	}

	int M_1 = (int)(LA + d_time2 - EA + d_time1) + 1;  // Big-M value
	
	// Penalty parameters for infeasibility handling
	double eplus = 500, emin = 500;
	double deltmin[C + 1];
	double deltplus[C + 1];

	deltmin[0] = -1100;
	deltplus[0] = -950;
	for (int i = 1; i < C + 1; i++) {
		deltmin[i] = 350;
		deltplus[i] = 450;
	}
	double nur = 50;
	bool stop2 = true;
	
	// Main column generation loop
	while ((reducedCost < -0.01 || stop2) && elapsed_time < 600) {
		std::cout << "Iteration:	" << it << " ---------------" << std::endl;
		
		// ====================================================================
		// MASTER PROBLEM - Select best subset of columns
		// ====================================================================
		IloEnv  env;
		IloModel model(env);

		// Variables: lambda[i] = 1 if column i is selected
		IloNumVarArray lambda(env);
		for (int i = 0; i < K; i++) {
			lambda.add(IloNumVar(env, 0, 1));
		}

		// Artificial variables for handling infeasibility
		IloNumVarArray yplus(env);
		for (int i = 0; i < C + 1; i++) {
			yplus.add(IloNumVar(env, 0, eplus));
		}

		IloNumVarArray ymin(env);
		for (int i = 0; i < C + 1; i++) {
			ymin.add(IloNumVar(env, 0, emin));
		}

		// OBJECTIVE: Minimize total cost
		IloExpr  SumL(env);

		// Travel time cost
		for (int i = 0; i < K; i++) {
			for (int j = 0; j < Stations; j++) {
				for (int k = 0; k < Stations; k++) {
					SumL += c1 * (double)yk[i][j][k] * (traveltimes[j][k] + delta) * lambda[i];
				}
				for (int p = 0; p < C; p++) {
					SumL += c1 * (double)xk[i][p][j] * tau * lambda[i];
				}
			}
		}

		// Walking time cost
		for (int i = 0; i < K; i++) {
			for (int p = 0; p < C; p++) {
				for (int j = 0; j < Stations; j++) {
					SumL += c2 * (double)xk[i][p][j] * traveltimep[p][j] * lambda[i];
				}
			}
		}

		// Waiting time cost
		for (int i = 0; i < K; i++) {
			for (int p = 0; p < C; p++) {
				SumL += c3 * (qk_early[i][p] + lvsea * qk_late[i][p]) * lambda[i];
			}
		}

		// Penalty for artificial variables
		for (int i = 0; i < C + 1; i++) {
			SumL += (deltplus[i] * yplus[i] - deltmin[i] * ymin[i]);
		}

		model.add(IloMinimize(env, SumL));
		SumL.end();

		// CONSTRAINTS
		IloRangeArray constraints(env, C + 1);
		IloNumArray duals(env, C + 1);

		// Constraint: Exactly nBuses routes must be selected
		IloExpr SumL1(env);
		for (int i = 0; i < K; i++) {
			SumL1 += lambda[i];
		}
		SumL1 += (yplus[0] - ymin[0]);
		IloRange sigma_constr(SumL1 == nBuses);
		constraints[0] = sigma_constr;
		model.add(sigma_constr);
		SumL1.end();

		// Constraint: Each passenger must be assigned exactly once
		for (const auto& p : P) {
			IloExpr sumX1(env);
			for (int i = 0; i < K; i++) {
				for (const auto& j : J) {
					sumX1 += xk[i][p][j] * lambda[i];
				}
			}
			sumX1 += (yplus[p + 1] - ymin[p + 1]);
			IloRange pip(sumX1 == 1);
			constraints[p + 1] = pip;
			model.add(pip);
			sumX1.end();
		}

		// SOLVE master problem
		IloCplex cplex(model);
		cplex.setParam(cplex.Threads, 12);
		cplex.setOut(env.getNullStream());
		cplex.solve();

		// Check if solution is feasible (no artificial variables used)
		stop2 = false;
		for (int i = 0; i < C + 1; i++) {
			if (cplex.getValue(ymin[i]) != 0 || cplex.getValue(yplus[i]) != 0) {
				stop2 = true;
				break;
			}
		}

		// Extract dual variables (shadow prices) for pricing problem
		try {
			cplex.getDuals(duals, constraints);
		}
		catch (IloException& e) {
			cerr << "IloException: " << e << endl;
		}
		catch (exception& e) {
			cerr << "Standard exception: " << e.what() << endl;
		}
		catch (...) {
			cerr << "Some other exception!" << endl;
		}

		sigma = duals[0];  // Dual for bus count constraint
		for (int p = 0; p < C; p++) {
			pi[p] = duals[p + 1];  // Duals for passenger constraints
		}

		double value = cplex.getObjValue();

		sigma_constr.end();
		constraints.end();
		duals.end();
		env.end();

		// ====================================================================
		// SUBPROBLEM (PRICING PROBLEM) - Generate new column with negative reduced cost
		// This finds the best new bus route that could improve the solution
		// ====================================================================
		IloEnv  env2;
		IloModel model2(env2);

		// VARIABLES
		IloArray<IloBoolVarArray> x(env2); // x[p][j] = 1 if passenger p assigned to station j
		for (int p = 0; p < C; p++) {
			x.add(IloBoolVarArray(env2, Stations));
		}

		IloArray<IloBoolVarArray> y(env2); // y[j][k] = 1 if arc from station j to k is used
		for (int j = 0; j < Stations; j++) {
			y.add(IloBoolVarArray(env2, Stations));
		}

		IloNumVar D(env2, 0, IloIntMax); // Departure delay from depot

		IloNumVarArray A(env2); // A[p] = arrival time for passenger p
		for (int p = 0; p < C; p++) {
			A.add(IloNumVar(env2, 0, IloIntMax));
		}

		IloNumVarArray q_early(env2); // Early arrival penalty
		for (int i = 0; i < C; i++) {
			q_early.add(IloNumVar(env2, 0, INFINITY));
		}
		
		IloNumVarArray q_late(env2); // Late arrival penalty
		for (int i = 0; i < C; i++) {
			q_late.add(IloNumVar(env2, 0, INFINITY));
		}

		// OBJECTIVE: Minimize reduced cost = cost - duals
		IloExpr  Travel_Walking_Time(env2);
		for (int j = 0; j < Stations; j++) {
			for (int k = 0; k < Stations; k++) {
				Travel_Walking_Time += c1 * y[j][k] * (traveltimes[j][k] + delta);
			}

			for (int p = 0; p < C; p++) {
				// Subtract dual variable pi[p] for assignment cost
				Travel_Walking_Time += x[p][j] * (c1 * (double)tau + c2 * traveltimep[p][j] - pi[p]);
			}
		}

		IloExpr  WaitingTime(env2);
		for (int p = 0; p < C; p++) {
			WaitingTime += c3 * (q_early[p] + lvsea * q_late[p]);
		}

		// Minimize: cost - sigma (dual for bus count)
		model2.add(IloMinimize(env2, Travel_Walking_Time + WaitingTime - sigma));
		Travel_Walking_Time.end();
		WaitingTime.end();

		// CONSTRAINTS

		// ROUTING CONSTRAINTS

		// At most one outgoing arc from optional stops
		for (int j = N; j < Stations; j++) {
			IloExpr sumY1(env2);
			for (int k = 0; k < Stations; k++) {
				sumY1 += y[j][k];
			}
			model2.add(sumY1 <= 1);
			sumY1.end();
		}

		// Exactly one outgoing/incoming arc for mandatory stops
		for (const auto& j : F) {
			if (j == N - 1) {  // Last station: one incoming arc
				IloExpr sumY1(env2);
				for (int k = 0; k < Stations; k++) {
					sumY1 += y[k][j];
				}
				model2.add(sumY1 == 1);
				sumY1.end();
			}
			else {  // Other mandatory: one outgoing arc
				IloExpr sumY2(env2);
				for (int k = 0; k < Stations; k++) {
					sumY2 += y[j][k];
				}
				model2.add(sumY2 == 1);
				sumY2.end();
			}
		}

		// No self-loops
		for (const auto& j : J) {
			model2.add(y[j][j] == 0);
		}

		// Flow conservation: what comes in must go out (except depot and final station)
		for (const auto& j : J) {
			if (j != 0 && j != N - 1) {
				IloExpr sumY1(env2);
				IloExpr sumY2(env2);
				for (int k = 0; k < Stations; k++) {
					sumY1 += y[j][k];
					sumY2 += y[k][j];
				}
				model2.add(sumY1 == sumY2);
				sumY1.end();
				sumY2.end();
			}
		}

		// No arcs from final station or to depot
		IloExpr sumY1(env2);
		IloExpr sumY2(env2);
		for (const auto& j : J) {
			sumY1 += y[N - 1][j];
			sumY2 += y[j][0];
		}
		model2.add(sumY1 == 0);
		model2.add(sumY2 == 0);
		sumY1.end();
		sumY2.end();

		// DEFINITION CONSTRAINTS

		// Binding: Optional station can only be visited if it has passengers
		for (int j = N; j < Stations; j++) {
			IloExpr sumX(env2);
			IloExpr sumY(env2);
			for (const auto& p : P) {
				sumX += x[p][j];
			}

			for (int l = 0; l < Stations; l++) {
				sumY += y[j][l];
			}

			model2.add(sumX <= bCapacity * sumY);
			sumX.end();
			sumY.end();
		}

		// Define arrival time variables
		for (int p = 0; p < C; p++) {
			IloExpr sumX1(env2);
			IloExpr sumX2(env2);
			IloExpr sumY(env2);

			for (const auto& j : J) {
				sumX2 += x[p][j];
				for (const auto& k : J) {
					sumY += (traveltimes[j][k] + delta) * y[j][k];
				}

				for (int c = 0; c < C; c++) {
					sumX1 += x[c][j] * tau;
				}
			}
			// Big-M constraints to define arrival time
			model2.add(sumY + sumX1 + D - A[p] <= (1 - sumX2) * M_1);
			model2.add(-sumY - sumX1 - D + A[p] <= (1 - sumX2) * M_1);
			model2.add(q_early[p] <= sumX2 * (d_time1));
			model2.add(q_late[p] <= sumX2 * (d_time2));
			sumX1.end();
			sumX2.end();
			sumY.end();
		}

		// CAPACITY CONSTRAINTS

		// Walking time threshold
		for (int p = 0; p < C; p++) {
			IloExpr sumX1(env2);
			for (const auto& j : J) {
				sumX1 += (traveltimep[p][j]) * x[p][j];
			}
			model2.add(sumX1 <= d);
			sumX1.end();
		}

		// Define waiting time based on arrival
		for (const auto& p : P) {
			model2.add(arrivals[p] - A[p] + q_late[p] - q_early[p] == 0);
		}

		// Bus capacity constraint
		IloExpr sumX(env2);
		for (const auto& j : J) {
			for (const auto& p : P) {
				sumX += x[p][j];
			}
		}
		model2.add(sumX <= bCapacity);
		sumX.end();

		// SOLVE pricing problem
		IloCplex cplex2(model2);
		cplex2.setParam(cplex2.Threads, 12);
		cplex2.setOut(env2.getNullStream());
		cplex2.setWarning(env2.getNullStream());
		cplex2.use(SubtourEliminationCallback(env2, y, Stations, N, C));
		cplex2.solve();

		// Extract solution from pricing problem
		vector<vector<bool>> xsol(C);
		vector<vector<bool>> ysol(Stations);
		double Dsol = cplex2.getValue(D);
		vector<double> Asol(C);
		vector<double> qsol_early(C);
		vector<double> qsol_late(C);

		for (int j = 0; j < Stations; j++) {
			vector<bool> ytemp(Stations);
			for (int k = 0; k < Stations; k++) {
				ytemp[k] = (int)cplex2.getValue(y[j][k] + 0.01);
			}
			ysol[j] = ytemp;
			ytemp.end();
		}

		for (int p = 0; p < C; p++) {
			vector<bool> xtemp(Stations);
			for (int k = 0; k < Stations; k++) {
				xtemp[k] = (int)cplex2.getValue(x[p][k] + 0.01);
			}
			xsol[p] = xtemp;
			xtemp.end();
		}

		for (int p = 0; p < C; p++) {
			Asol[p] = cplex2.getValue(A[p]);
			qsol_late[p] = cplex2.getValue(q_late[p]);
			qsol_early[p] = cplex2.getValue(q_early[p]);
		}

		reducedCost = cplex2.getObjValue();

		env2.end();

		// UPDATE penalty parameters
		if (it % 2 == 0) {
			emin -= 5;
			eplus -= 5;
			if (emin < 0) emin = 0;
			if (eplus < 0) eplus = 0;
		}
		
		if ((int)(reducedCost + 0.1) >= 0) {
			// Update delta values based on duals
			for (int i = 1; i < C + 1; i++) {
				deltmin[i] = pi[i - 1] - nur;
				deltplus[i] = pi[i - 1] + nur;
			}
			deltmin[0] = sigma - nur;
			deltplus[0] = sigma + nur;
		}

		// Add new column to pool
		xk.push_back(xsol);
		yk.push_back(ysol);
		Ak.push_back(Asol);
		Dk.push_back(Dsol);
		qk_early.push_back(qsol_early);
		qk_late.push_back(qsol_late);
		K++;
		it++;

		elapsed_time = (double)(clock() - start_time) / CLOCKS_PER_SEC;
	}
	
	// ========================================================================
	// FINAL INTEGER MASTER PROBLEM - Select integer solution
	// ========================================================================
	IloEnv  env;
	IloModel model(env);

	//Variables ------------------------
	IloBoolVarArray lambda(env); //lambda variable
	for (int i = 0; i < K; i++) {
		lambda.add(IloBoolVar(env));
	}


	// OBJECTIVE -------------------------------------------------------
	IloExpr  SumL(env);

	//Travel time 
	for (int i = 0; i < K; i++) {
		for (int j = 0; j < Stations; j++) {
			for (int k = 0; k < Stations; k++) {
				SumL += c1 * (double)yk[i][j][k] * (traveltimes[j][k] + delta) * lambda[i];
			}
			for (int p = 0; p < C; p++) {
				SumL += c1 * (double)xk[i][p][j] * tau * lambda[i];
			}
		}
	}

	//Walking Time
	for (int i = 0; i < K; i++) {
		for (int p = 0; p < C; p++) {
			for (int j = 0; j < Stations; j++) {
				SumL += c2 * (double)xk[i][p][j] * (traveltimep[p][j]) * lambda[i];
			}
		}
	}

	//  Waiting Time;
	for (int i = 0; i < K; i++) {
		for (int p = 0; p < C; p++) {
			SumL += c3 * (qk_early[i][p] + lvsea * qk_late[i][p]) * lambda[i];
		}
	}


	model.add(IloMinimize(env, SumL));
	SumL.end();


	//CONSTRAINTS-------------------------------------------------------

	IloExpr SumL1(env);
	for (int i = 0; i < K; i++) {
		SumL1 += lambda[i];
	}
	model.add(SumL1 == nBuses);
	SumL1.end();

	// All passengers need a bus 
	for (const auto& p : P) {
		IloExpr sumX1(env);
		for (int i = 0; i < K; i++) {
			for (const auto& j : J) {
				sumX1 += xk[i][p][j] * lambda[i];
			}
		}
		model.add(sumX1 == 1);
		sumX1.end();
		//pip.end();
	}


	//SOLVE----------------------------
	IloCplex cplex(model);
	cplex.setOut(env.getNullStream());
	cplex.solve();
	elapsed_time = (double)(clock() - start_time) / CLOCKS_PER_SEC;
	
	// ========================================================================
	// OUTPUT RESULTS
	// ========================================================================
	std::cout << "\n****************\nComputational time: " << elapsed_time << " seconds " << endl << endl;
	std::cout << "Final Objective Value: " << cplex.getObjValue() << endl;
	std::cout << "Optimality Gap: " << -reducedCost / cplex.getObjValue() * 100.0 << " % \n****************\n " << endl;

	// Extract final solution
	int xsol[C][nBuses][Stations];
	ofstream txt_xsol("data/output/xsol.txt");
	int ysol[nBuses][Stations][Stations];
	ofstream txt_ysol("data/output/ysol.txt");
	double Dsol[nBuses];
	ofstream txt_Dsol("data/output/Dsol.txt");
	double Asol[C];
	ofstream txt_Asol("data/output/Asol.txt");

	int ii = 0;
	for (int i = 0; i < K; i++) {
		if ((int)cplex.getValue(lambda[i] + 0.001) == 1) {
			std::cout << "- Lambda_" << i << " :" << cplex.getValue(lambda[i]) << endl;
			std::cout << "-- Bus index: " << ii << endl;
			Dsol[ii] = Dk[i];
			txt_Dsol << Dsol[ii] << endl;

			txt_xsol << "Bus " << i << endl;
			txt_ysol << "Bus " << i << endl;
			
			// Write routing and assignment solutions
			for (int j = 0; j < Stations; j++) {
				for (int k = 0; k < Stations; k++) {
					ysol[ii][j][k] = yk[i][j][k];
					txt_ysol << ysol[ii][j][k] << " ";
				}
				for (int p = 0; p < C; p++) {
					xsol[p][ii][j] = xk[i][p][j];
					txt_xsol << xsol[p][ii][j] << " ";
				}
				txt_xsol << endl;
				txt_ysol << endl;
			}
			txt_xsol << "end" << endl;
			txt_ysol << "end" << endl;

			// Extract passenger arrival times
			for (int p = 0; p < C; p++) {
				int sumX2 = 0;
				for (const auto& j : J) {
					sumX2 += xk[i][p][j];
				}
				if (sumX2 == 1) {
					Asol[p] = Ak[i][p];
				}
			}
			ii++;
		}
	}

	for (int p = 0; p < C; p++) {
		txt_Asol << Asol[p] << endl;
	}

	env.end();
	txt_xsol.close();
	txt_ysol.close();
	txt_Asol.close();
	txt_Dsol.close();

	// ========================================================================
	// PRINT SOLUTION SUMMARY
	// ========================================================================
	std::cout << "\n---------- Bus Departure Times (seconds) -------- " << endl;
	for (int i = 0; i < nBuses; i++) {
		std::cout << "Bus " << i << " --> " << Dsol[i] << "s" << endl;
	}
	
	std::cout << "\n---------- Passenger Waiting Times (seconds) --------- " << endl;
	for (int p = 0; p < C; p++) {
		std::cout << "Passenger " << p << " --> " << arrivals[p] - Asol[p] << "s" << endl;
	}
	std::cout << endl;

	// ========================================================================
	// WRITE DETAILED OUTPUT FILES
	// ========================================================================
	
	// Write station visit times for each bus
	ofstream txt_visits("data/output/visits.txt");
	j = 0;
	double travel = 0;
	for (int i = 0; i < nBuses; i++) {
		j = 0;
		travel = Dsol[i];
		txt_visits << "Bus " << i + 1 << endl;
		
		// Trace route from depot to final station
		while (j != N - 1) {
			for (int k = 0; k < Stations; k++) {
				if (ysol[i][j][k] == 1) {
					txt_visits << j << " " << travel << endl;
					travel += (traveltimes[j][k] + delta);
					// Add dwell time for passengers boarding
					for (int p = 0; p < C; p++) {
						travel += xsol[p][i][j] * tau;
					}
					j = k;
				}
			}
		}
		txt_visits << j << " " << travel << endl;
		txt_visits << "end" << endl;
	}
	txt_visits.close();

	// Write walking times for each passenger
	ofstream txt_walking("data/output/walking.txt");
	for (int p = 0; p < C; p++) {
		for (int j = 0; j < Stations; j++) {
			for (int i = 0; i < nBuses; i++) {
				if (xsol[p][i][j] == 1) {
					txt_walking << j << " " << traveltimep[p][j] << endl;
				}
			}
		}
	}
	txt_walking.close();
}
