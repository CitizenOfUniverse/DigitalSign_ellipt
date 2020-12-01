//#define all(x) (x).begin(), (x).end()
//#define rall(x) (x).rbegin(), (x).rend()
#define forall(it, x) for(auto it = (x).begin(); it != (x).end(); it++)
//#define OUT(x) {cout << x; exit(0);}
//#define sz size()
#define ft first
#define sd second
#define pb(x) push_back(x)
//#define pb2(x, y) push_back(x, y)
#define mp(x, y) make_pair(x, y)
#define fora0(ITER, LIMIT) for(int ITER = 0; ITER < LIMIT; ITER++)
//#define fora1(ITER, LIMIT) for(int ITER = 1; ITER <= LIMIT; ITER++)
//#define ford0(ITER, LIMIT) for(int ITER = LIMIT - 1; ITER >= 0; ITER--)
//#define ford1(ITER, LIMIT) for(int ITER = LIMIT; ITER >= 1; ITER--)

#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <map>
#include <string>
#include <iomanip>
#include "assert.h"
#include <stack>
#include <queue>
#include <set>
#include <cstdio>
#include <array>
#include <list>
#include <sstream>

#pragma GCC optimize("Ofast")
#pragma GCC optimize("unroll-loops")

using namespace::std;

typedef long long ll;
typedef long long ull;
typedef long double ld;
typedef pair<int, int> pii;
typedef pair<ll, ll> pll;
typedef unsigned int uint;

//const int INF = numeric_limits<int>::max() / 10;
//const ll INFn = numeric_limits<ll>::min();
//const ll ll_INFn = numeric_limits<ll>::min() / 10;

void problem();

int main() {
	//#ifdef _DEBUG
	//	freopen("input.txt", "r", stdin);
	//	freopen("output.txt", "w", stdout);
	//#endif
	ios_base::sync_with_stdio(false);
	cin.tie(0);
#ifdef _DEBUG
	int tstn = 1;
	while (tstn--) {
#endif
		problem();
#ifdef _DEBUG
		cout << '\n';
	}
#endif
	return 0;
}

ll bin_pow(ll a, ll b, ll p) {
	if (b == 0) {
		return 1;
	}
	ll aa = bin_pow(a, b / 2, p);
	aa = (aa * aa) % p;
	if (b % 2 == 1) {
		aa = (aa * a) % p;
	}
	return aa;
}

ll rev_mod(ll a, ll p) {
	return bin_pow(a, p - 2, p);
}

pii add(ll x1, ll y1, ll x2, ll y2, ll p, ll a, ll b) {
	//Considering operations with neutral element of group - 
	//infinetely far point
	if (x1 == -1 && y1 == -1) {
		return mp(x2, y2);
	}
	if (x2 == -1 && y2 == -1) {
		return mp(x1, y1);
	}
	ll lambda;
	//cout << "Adding (" << x1 << ", " << y1 << ") to (" << x2 << ", " << y2 << "):\n";
	if (x1 != x2 || y1 != y2) {
		//cout << "P != Q - formula 1\n";
		//cout << "Lambda Numerator is " << y2 << " - " << y1 << " = ";
		ll num = (y2 - y1 + p) % p;
		//cout << num << '\n';
		//cout << "Lambda Denominator is " << x2 << " - " << x1 << " = ";
		ll denom = (x2 - x1 + p) % p;
		//cout << denom << '\n';
		if (denom == 0) {
			//cout << "Result is infinitily far point\n\n";
			return mp(-1, -1);
		}
		ll numm = rev_mod(denom, p);
		//cout << "Reverse to " << denom << " is " << numm << '\n';
		//cout << "Lambda = " << num << " * " << numm << " = ";
		lambda = (num * numm) % p;
		//cout << lambda << '\n';
	}
	else {
		//cout << "P == Q - formula 2\n";
		//cout << "Lambda Numerator is (3*(" << x1 << ")^2 + ("
		//	<< a << ") = ";
		ll num = (3 * x1 * x1 + a + p) % p;
		//cout << num << '\n';
		//cout << "Lambda Denominator is 2 * " << y1 << " = ";
		ll denom = (2 * y1) % p;
		//cout << denom << '\n';
		if (denom == 0) {
			//cout << "Result is infinitily far point\n\n";
			return mp(-1, -1);
		}
		ll numm = rev_mod(denom, p);
		//cout << "Reverse to " << denom << " is " << numm << '\n';
		//cout << "Lambda = " << num << " * " << numm << " = ";
		lambda = (num * numm) % p;
		//cout << lambda << '\n';
	}
	//cout << "Resulting point is:\n";
	//cout << "x3 = lambda^2-x1-x2 = ";
	ll x3 = (lambda * lambda - x1 - x2 + 2 * p) % p;
	//cout << x3 << '\n';
	//cout << "y3 = lambda * (x1-x3) - y1 = ";
	ll y3 = (lambda * (x1 - x3 + p) - y1 + p) % p;
	//cout << y3 << "\n\n";
	return mp(x3, y3);
}

pii add(pii p1, pii p2, ll p, ll a, ll b) {
	return add(p1.ft, p1.sd, p2.ft, p2.sd, p, a, b);
}

pii bin_add_points(pii p1, int power, ll p, ll a, ll b) {
	if (power == 0) {
		//Neutral element
		return mp(-1, -1);
	}
	pii p1_sq = bin_add_points(p1, power / 2, p, a, b);
	p1_sq = add(p1_sq.ft, p1_sq.sd, p1_sq.ft, p1_sq.sd, p, a, b);
	if (power % 2 == 1) {
		p1_sq = add(p1_sq.ft, p1_sq.sd, p1.ft, p1.sd, p, a, b);
	}
	return p1_sq;
}

void find_all(ll a, ll b, ll p) {
	vector<ll> y(p), fun(p);
	fora0(i, p) {
		y[i] = (i * i) % p;
		fun[i] = (i * i * i + (p + a) * i + b + p) % p;
	}
	vector<pll> res;
	fora0(j, p) {
		fora0(i, p) {
			if (y[i] == fun[j]) {
				res.pb(mp(j, i));
			}
		}
	}
	sort(res.begin(), res.end());
	cout << "Points of elleptical curve:\n";
	fora0(i, res.size()) {
		cout << "(" << res[i].ft << ", " << res[i].sd << ")\n";
	}
	cout << '\n';
	//fora0(i, res.size()) {
	//	cout << setw(5) << res[i].sd << ' ';
	//}
}

//(r, s) - digital signature
//h - message digest
//p, a, b - parameters of elliptic curve E_p(a, b)
//G - generating point of curve
//q - order of the generating point
//Q - public key (for digital signature check)
bool check_digital_sign(ll r, ll s, ll h, ll p, ll a, ll b, pii G, ll q, pii Q) {
	if (!(1 <= r && r <= q - 1) || !(1 <= s && s <= q - 1)) {
		return false;
	}
	ll v = rev_mod(s, q);
	ll u1 = (r * h) % q;
	ll u2 = (r * v) % q;
	pii X = add(bin_add_points(G, u1, p, a, b), bin_add_points(Q, u2, p, a, b), p, a, b);
	ll x = X.ft, y = X.sd;
	return r == x % q;
}

//h - message digest
//d - secret key
//k - "fixed" random number
//p, a, b - parameters of elliptic curve E_p(a, b)
//G - generating point of curve
//q - order of the generating point
pii gen_digital_sign(ll h, ll d, ll k, ll p, ll a, ll b, pii G, ll q) {
	pii kG = bin_add_points(G, k, p, a, b);
	ll x = kG.ft, y = kG.sd;
	ll r = x % q;
	if (r == 0) {
		//k value is incorrect
		return mp(-1, -1);
	}
	ll z = rev_mod(k, q);
	ll s = z * (h + (d * r) % q) % q;
	if (s == 0) {
		//k value is incorrect
		return mp(-1, -1);
	}
	return mp(r, s);
}

void problem() {
	string cmd = "menu";
	while (cmd != "exit") {
		if (cmd == "menu") {
			cout << "\n\nmenu - show this menu\n" <<
				"gen_DS - generate digital signature (via elliptic curves cryptography methods\n" <<
				"check_DS - verify digital signature\n" <<
				"exit - exit program\n\n";
		}
		else if (cmd == "gen_DS") {
			ll h, d, k, p, a, b;
			pii G;
			ll q;
			cout << "Enter parameters h, d, k, p, a, b, G.x, G.y, q\nwhere:\n";
			cout << "h - message digest\n" <<
				"d - secret key\n" <<
				"k - \"fixed\" random number\n" <<
				"p, a, b - parameters of elliptic curve E_p(a, b)\n" <<
				"G - generating point of curve\n" <<
				"q - order of the generating point\n\n";
			cin >> h >> d >> k >> p >> a >> b >> G.ft >> G.sd >> q;
			if (a < 0) {
				a = (a + p) % p;
			}
			if (b < 0) {
				b = (b + p) % p;
			}
			pii sign = gen_digital_sign(h, d, k, p, a, b, G, q);
			cout << "Digital sign:\n(" << sign.ft << ", " << sign.sd << ")\n\n";
		}
		else if (cmd == "check_DS") {
			ll r, s, h, p, a, b;
			pii G;
			ll q;
			pii Q;
			cout << "Enter parameters r, s, h, p, a, b, G.x, G.y, q, Q.x, Q.y\nwhere:\n";
			cout << "(r, s) - digital signature\n" <<
				"h - message digest\n" <<
				"p, a, b - parameters of elliptic curve E_p(a, b)" <<
				"G - generating point of curve" <<
				"q - order of the generating point" <<
				"Q - public key (for digital signature check)\n\n";
			cin >> r >> s >> h >> p >> a >> b >> G.ft >> G.sd >> q >> Q.ft >> Q.sd;
			if (a < 0) {
				a = (a + p) % p;
			}
			if (b < 0) {
				b = (b + p) % p;
			}
			cout << (check_digital_sign(r, s, h, p, a, b, G, q, Q) ? "Signature is correct\n\n" : "Signature is illegal\n\n");
		}
		else if (cmd == "add") {
			ll p;
			//y=x^3+a*x+b
			ll a, b;
			cout << "Enter module p:\n";
			cin >> p;
			cout << "Enter a, b:\n";
			cin >> a >> b;
			cout << "Curve is y=x^3+(" << a << ")*x+(" << b << ")\n";
			ll x1, y1, x2, y2;
			cout << "Enter x1, y1, x2, y2:\n";
			cin >> x1 >> y1 >> x2 >> y2;
			pii res = add(x1, y1, x2, y2, p, a, b);
		}
		else if (cmd == "findall") {
			ll p;
			//y=x^3+a*x+b
			ll a, b;
			cout << "Enter module p:\n";
			cin >> p;
			cout << "Enter a, b:\n";
			cin >> a >> b;
			cout << "Curve is y=x^3+(" << a << ")*x+(" << b << ")\n";
			find_all(a, b, p);
		}
		else if (cmd == "exit") {
			cout << "Thanks for work. Goodbye\n\n";
			break;
		}
		else {
			cout << "Incorrect command. Please, try again\n\n";
		}
		cin >> cmd;
		/*if (cmd == "Default") {
			cout <<
		}*/
	}
	return;
}
