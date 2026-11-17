#include <iostream>
#include <vector>
#include <queue>
#include <string>
#include <algorithm>
#include <climits>
#include <stdexcept>
using namespace std;

typedef long long ll;
const ll INF = LLONG_MAX / 4;
const int MAX_PATIENTS = 18;

// Prevents distance addition from overflowing.
ll safeAdd(ll a, ll b) {
    if (a >= INF || b >= INF || a > INF - b) return INF;
    return a + b;
}

// Finds the position of the lowest set bit.
int lowBit(unsigned int x) {
#ifdef __GNUC__
    return __builtin_ctz(x);
#else
    int pos = 0;
    while ((x & 1U) == 0) {
        x >>= 1;
        pos++;
    }
    return pos;
#endif
}

class Graph {
    struct Edge {
        int to;
        ll weight;
    };

    int V;
    vector<vector<Edge> > adj;

public:
    Graph(int vertices) : V(vertices), adj(vertices) {}

    void addEdge(int u, int v, ll w) {
        adj[u].push_back({v, w});
        adj[v].push_back({u, w}); // Undirected graph.
    }

    // Dijkstra finds shortest distances from one source.
    void dijkstra(int source, const vector<char>& isTarget,
                  int targetCount, vector<ll>& dist,
                  vector<int>& parent) const {
        dist.assign(V, INF);
        parent.assign(V, -1);
        vector<char> done(V, false);
        priority_queue<pair<ll, int>,
            vector<pair<ll, int> >,
            greater<pair<ll, int> > > pq;

        dist[source] = 0;
        pq.push({0, source});

        while (!pq.empty()) {
            ll d = pq.top().first;
            int u = pq.top().second;
            pq.pop();

            if (done[u]) continue; // Ignore outdated entries.
            done[u] = true;

            if (isTarget[u]) {
                targetCount--;
                if (targetCount == 0) break; // All required destinations reached.
            }

            for (size_t i = 0; i < adj[u].size(); i++) {
                int v = adj[u][i].to;
                ll w = adj[u][i].weight;
                ll newDist = safeAdd(d, w);

                if (newDist < dist[v]) {
                    dist[v] = newDist;
                    parent[v] = u;
                    pq.push({newDist, v});
                }
            }
        }
    }
};

class RoundPlanner {
    const Graph& graph;
    vector<string> names;
    vector<int> keys; // keys[0] = nurse station; remaining keys = patients.
    vector<vector<ll> > D;
    vector<vector<int> > parents;

    // Builds shortest distances between every pair of important locations.
    void buildDistanceMatrix() {
        int m = (int)keys.size();
        int V = (int)names.size();
        D.assign(m, vector<ll>(m, INF));
        parents.assign(m, vector<int>());

        vector<char> isTarget(V, false);
        for (int i = 0; i < m; i++)
            isTarget[keys[i]] = true;

        for (int i = 0; i < m; i++) {
            vector<ll> dist;
            graph.dijkstra(keys[i], isTarget, m, dist, parents[i]);

            for (int j = 0; j < m; j++) {
                D[i][j] = dist[keys[j]];
                if (D[i][j] >= INF)
                    throw runtime_error("Some important locations are unreachable.");
            }
        }
    }

public:
    RoundPlanner(const Graph& g, const vector<string>& nodeNames,
                 int depot, const vector<int>& patients)
        : graph(g), names(nodeNames) {
        keys.push_back(depot);
        for (size_t i = 0; i < patients.size(); i++)
            keys.push_back(patients[i]);

        buildDistanceMatrix();
    }

    // Held-Karp DP finds the globally shortest visiting order.
    pair<ll, vector<int> > solveDP() const {
        int k = (int)keys.size() - 1;
        if (k == 0) return {0, vector<int>{0, 0}};

        int totalMasks = 1 << k;
        int FULL = totalMasks - 1;

        // dp[mask][i] = minimum cost to visit mask and finish at patient i.
        vector<ll> dp((size_t)totalMasks * k, INF);
        vector<signed char> from((size_t)totalMasks * k, -1);

        #define DP(mask, i) dp[(size_t)(mask) * k + (i)]
        #define FROM(mask, i) from[(size_t)(mask) * k + (i)]

        for (int i = 0; i < k; i++)
            DP(1 << i, i) = D[0][i + 1]; // Start from the nurse station.

        for (int mask = 1; mask <= FULL; mask++) {
            unsigned int remaining = (unsigned int)mask;

            while (remaining) {
                int i = lowBit(remaining);
                remaining &= remaining - 1;

                int previousMask = mask ^ (1 << i);
                if (previousMask == 0) continue;

                unsigned int previous = (unsigned int)previousMask;

                while (previous) {
                    int j = lowBit(previous);
                    previous &= previous - 1;

                    ll candidate = safeAdd(DP(previousMask, j),
                                           D[j + 1][i + 1]);

                    if (candidate < DP(mask, i)) {
                        DP(mask, i) = candidate;
                        FROM(mask, i) = (signed char)j;
                    }
                }
            }
        }

        ll best = INF;
        int last = -1;

        // Add the return journey to the nurse station.
        for (int i = 0; i < k; i++) {
            ll candidate = safeAdd(DP(FULL, i), D[i + 1][0]);
            if (candidate < best) {
                best = candidate;
                last = i;
            }
        }

        if (last == -1 || best >= INF)
            throw runtime_error("No valid complete tour exists.");

        // Reconstruct the optimal visiting order.
        vector<int> route;
        int mask = FULL;
        int current = last;

        while (current != -1) {
            route.push_back(current + 1);
            int previous = FROM(mask, current);
            mask ^= (1 << current);
            current = previous;
        }

        reverse(route.begin(), route.end());
        route.insert(route.begin(), 0);
        route.push_back(0);

        #undef DP
        #undef FROM

        return {best, route};
    }

    // Greedy chooses the nearest unvisited patient at every step.
    pair<ll, vector<int> > solveGreedy() const {
        int k = (int)keys.size() - 1;
        vector<char> visited(k + 1, false);
        vector<int> route(1, 0);

        int current = 0;
        ll total = 0;

        for (int step = 0; step < k; step++) {
            int next = -1;
            ll best = INF;

            for (int j = 1; j <= k; j++) {
                if (!visited[j] && D[current][j] < best) {
                    best = D[current][j];
                    next = j;
                }
            }

            if (next == -1 || best >= INF)
                throw runtime_error("No valid greedy tour exists.");

            visited[next] = true;
            total = safeAdd(total, best);
            route.push_back(next);
            current = next;
        }

        total = safeAdd(total, D[current][0]);
        route.push_back(0); // Return to the nurse station.

        return {total, route};
    }

    // Prints only the scheduled visiting order.
    void visitOrder(const vector<int>& route) const {
        for (size_t i = 0; i < route.size(); i++) {
            if (i) cout << " -> ";
            cout << names[keys[route[i]]];
        }
        cout << '\n';
    }

    // Reconstructs the actual shortest physical path between stops.
    void describe(const vector<int>& route) const {
        vector<int> physical;

        for (size_t i = 0; i + 1 < route.size(); i++) {
            int from = route[i];
            int to = route[i + 1];

            vector<int> segment;
            int v = keys[to];
            int source = keys[from];

            while (v != source) {
                segment.push_back(v);
                v = parents[from][v];

                if (v == -1)
                    throw runtime_error("Could not reconstruct physical route.");
            }

            segment.push_back(source);
            reverse(segment.begin(), segment.end());

            // Avoid printing the connecting location twice.
            if (!physical.empty()) segment.erase(segment.begin());

            physical.insert(physical.end(), segment.begin(), segment.end());
        }

        for (size_t i = 0; i < physical.size(); i++) {
            if (i) cout << " -> ";
            cout << names[physical[i]];
        }
        cout << '\n';
    }
};

int main() {
    try {
        int V, E;

        cout << "Enter number of locations: ";
        if (!(cin >> V) || V <= 0)
            throw runtime_error("Invalid number of locations.");

        vector<string> names(V);
        cout << "Enter location names (use underscores for spaces):\n";

        for (int i = 0; i < V; i++) {
            cin >> names[i];
            replace(names[i].begin(), names[i].end(), '_', ' ');
        }

        cout << "Enter number of roads: ";
        if (!(cin >> E) || E < 0)
            throw runtime_error("Invalid number of roads.");

        Graph graph(V);
        cout << "Enter each road as: location1 location2 distance\n";

        for (int i = 0; i < E; i++) {
            int u, v;
            ll w;

            if (!(cin >> u >> v >> w))
                throw runtime_error("Invalid road input.");

            if (u < 0 || u >= V || v < 0 || v >= V ||
                w < 0 || w >= INF)
                throw runtime_error("Invalid road details.");

            graph.addEdge(u, v, w);
        }

        int depot, k;
        cout << "Enter nurse station index: ";
        if (!(cin >> depot) || depot < 0 || depot >= V)
            throw runtime_error("Invalid nurse station index.");

        cout << "Enter number of patients: ";
        if (!(cin >> k) || k < 0 || k > MAX_PATIENTS || k >= V)
            throw runtime_error("Patient count must be between 0 and 18, and less than the number of locations.");

        vector<int> patients;
        vector<char> used(V, false);
        used[depot] = true;

        cout << "Enter patient location indices:\n";
        for (int i = 0; i < k; i++) {
            int p;
            cin >> p;

            if (!cin || p < 0 || p >= V || used[p])
                throw runtime_error("Invalid or duplicate patient location.");

            used[p] = true;
            patients.push_back(p);
        }

        RoundPlanner planner(graph, names, depot, patients);

        pair<ll, vector<int> > exact = planner.solveDP();
        pair<ll, vector<int> > greedy = planner.solveGreedy();

        cout << "\n====================================\n";
        cout << "       EXACT HELD-KARP DP RESULT\n";
        cout << "====================================\n";
        cout << "Visiting order:\n";
        planner.visitOrder(exact.second);
        cout << "\nActual physical route:\n";
        planner.describe(exact.second);
        cout << "\nMinimum total distance: " << exact.first << '\n';

        cout << "\n====================================\n";
        cout << "      GREEDY NEAREST NEIGHBOUR\n";
        cout << "====================================\n";
        cout << "Visiting order:\n";
        planner.visitOrder(greedy.second);
        cout << "\nActual physical route:\n";
        planner.describe(greedy.second);
        cout << "\nGreedy total distance: " << greedy.first << '\n';

        cout << "\n====================================\n";
        cout << "          FINAL COMPARISON\n";
        cout << "====================================\n";
        cout << "Exact DP distance: " << exact.first << '\n';
        cout << "Greedy distance: " << greedy.first << '\n';

        if (greedy.first == exact.first) {
            cout << "\nBoth algorithms found tours of equal length.\n";
        } else {
            double gap = (double)(greedy.first - exact.first)
                         / exact.first * 100.0;
            cout << "\nGreedy is " << gap
                 << "% longer than the optimal DP tour.\n";
        }

        cout << "\n====================================\n";
        cout << "              COMPLETE\n";
        cout << "====================================\n";
    }
    catch (const exception& e) {
        cerr << "\nError: " << e.what() << '\n';
        return 1;
    }

    return 0;
}
