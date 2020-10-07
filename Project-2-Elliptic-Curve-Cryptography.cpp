#include <bits/stdc++.h>

#define LHS(Y) (quad(Y))
#define RHS(X) ((cub((X)) + coe[2]*quad((X)) + coe[1]*(X) + coe[0]) % p)

using namespace std;

typedef pair<int, int> int_pair;

const int MAXN = 100005; // the maximum number of entries the array could register in this program
const int_pair INF = make_pair(MAXN, MAXN); // the point at infinity

int coe[3]; //coefficients of the elliptic curve - a = coe[2], b = coe[1], c = coe[0]
int flag = false;
char poly[MAXN] = {'\0'}; // the string used to read the elliptic curve

int p;
int prc[MAXN]; // store results of the sieve - if n is prime, prc[n] = 1

int cnt_p = 1;
map< int_pair, int > points; // use a map structure to store information of points on the curve

int inv[MAXN]; // inv[n] store the multiplicative inverse of n

int cub(int x) {return (x * x * x) % p;}
int quad(int x) {return (x * x) % p;}

void readCoe(int o, int l, int r) { // read the numbers in the parentheses
  int res = 0, sgn = 1;
  if(poly[l] == '-') {
    sgn = -1;
    ++l;
  }
  if(poly[l] == '+') ++l;
  for(int i = l;i < r;++i) {
    if(poly[i] < '0' || poly[i] > '9') flag = true;
    res = res * 10 + (poly[i] - '0');
  }
  coe[o] = sgn * res;
  return;
}

void readPoly() { // locate the parentheses
  int len = strlen(poly);
  int cnt = 0, part[15][2];
  memset(part, -1, sizeof(part));
  for(int i = 0;i < len;++i) {
    if(poly[i] == '(') {
      if(part[cnt][0] == -1) part[cnt][0] = i;
      else return;
    }
    if(poly[i] == ')') {
      if(part[cnt][0] != -1 && part[cnt][1] == -1) {
        part[cnt][1] = i;
        ++cnt;
      }
    }
  }
  if(cnt != 3) return;
  for(int i = 0;i < cnt;++i) readCoe(cnt - i - 1, part[i][0] + 1, part[i][1]);
  flag = !flag; 
  /*
    - if flag is false (the original setup), then it should be true;
    - if flag is set true in readCoe(), then the substring between a pair of parentheses is not a legal number, thus it should be false.
  */
  return;
}

bool isPrime(int n) { // check if n is prime by Sieve of Eratosthenes
  if(prc[n] != -1) return prc[n];
  for(int i = 2;i <= n;++i) {
    if(prc[i] != 0) { // if it is not sieved yet, i should be prime
      for(int j = 2;i * j <= n;++j) 
        prc[i * j] = 0; // the multiplier of a prime is surely not a prime
      prc[i] = 1; // mark i as a prime
    }
  }
  return prc[n];
}

void initiate() { // input the elliptic curve and prime
  memset(prc, -1, sizeof(prc));
  memset(inv, -1, sizeof(inv));
  cout << "Input the elliptic curve:" << endl;
  cout << "( Parentheses are mandatory for enclosing the coefficients" << endl;
  cout << ".e.g y^2 = x^3 + (0)x^2 + (-123)x + (1) )" << endl;
  cin.getline(poly, MAXN);
  readPoly();
  while(!flag) { // increase robustness of input
    cout << "The input is invalid. Please input again:" << endl;
    cin.getline(poly, MAXN);
    readPoly();
  }
  cout << endl << "Input the prime P(P < " << MAXN << "): ";
  cin >> p;
  while(!isPrime(p)) { // increase robustness of input
    cout << p << " is not a prime. Please input again: ";
    cin >> p;
  }
  cout << endl;
  return;
}

int mod(int b) {return (b % p < 0) ? (b % p + p) : (b % p);}

void compPoints() {
  for(int i = 0;i < p && cnt_p <= p - 1;++i) { 
    // by Bezout's theorem, there should be atmost 3p points on the elliptic curve (of degree 3) over Z/pZ
    for(int j = 0;j < p && cnt_p <= p - 1;++j) {
      if(mod(LHS(j)) == mod(RHS(i))) {
        points.insert({make_pair(i, j), cnt_p + 1});
        cnt_p++;
      }
    }
  }
}

void printPoints() { // print the points computed
  cout << "Do you want to print the points on the ellitpic curve over Z/pZ? (Y/n)" << endl;
  char IN;
  cin >> IN;
  cout << endl;
  if(!(IN == 'Y' || IN == 'y')) return;
  printf("The following are %d points of the elliptic curve C: %s over Z/(%d)Z: \n", cnt_p, poly, p);
  printf("1:  0 (the point at infinity)\n");
  for(auto itr = points.begin();itr != points.end();itr++)
    printf("%d: (%d, %d)\n", itr->second, itr->first.first, itr->first.second);
  printf("\n");
}

int exgcd(int a, int b, int &x, int &y) {
  if(b == 0) { // terminate condition of the iteration
    x = 1;
    y = 0;
    return a;
  }
  int r = exgcd(b, a % b, x, y);
  int t = y;
  y = x - (a / b) * y;
  x = t;
  /*
    We want to solve for x' * a' + y' * b' = d.
    We have x * a + y * a = d, a = b', b = a' - [a' / b'] * b'
    Thus x * (b') + y * (a' - [a' / b'] * b') = d
      => (y) * a' + (x - y * [a' / b']) * b' = d
    That is to say x' = y, y' = x - y * [a' / b'].
  */
  return r;
}

int mod_div(int a, int b) {
  a = mod(a);
  b = mod(b); // make sure b is not lease than 0
  // find the multiplicative inverse of b in Z/pZ
  if(inv[b] != -1) return mod(a * inv[b]);
  // to find bx = 1 (mod p), is to solve the equation kp - bx = 1 <=> p|(bx - 1)
  // we can use the extended euclidean algorithm to solve this at the first time
  int k, x;
  exgcd(p, b, k, x);
  inv[b] = mod(x);
  return mod(a * inv[b]);
}

/*
int_pair addition2(int_pair P, int_pair Q) {
  if(P.first == Q.first && P.second == -1 * Q.second) 
    return INF; // if P = -Q, then P + Q = 0 at the infinity
  if(P == INF) return Q;
  if(Q == INF) return P;
  if(P == Q) { // P + P is the additive inverse of the point at which the curve and the tangent cross P intersects
    if(P.second == 0) return INF; // the case when the tangent is of a slope of 0, then the tangent cross 0 at the infinity
    int u = P.first, v = P.second;
    int C = mod_div(3*quad(u) + 2*coe[2]*u + coe[1], 2*v);
    int_pair res;
    res.first = quad(C) - coe[2] - 2*u;
    res.second = -1*C*(res.first) - v + C*u;
    res.first = mod(res.first);
    res.second = mod(res.second);
    return res;
  }
  if(P.first == Q.first) return INF; // if P, Q has the same x coordinate but the different y coordinate (or else the function would return the result before), then Q is the additive inverse of Q, thus P + Q == 0 at the infinity. 
  // the rest cases are normal, we only need to use the addition formula
  int u = P.first, v = P.second, w = Q.first, z = Q.second;
  int C = mod_div(z - v, w - u);
  int_pair res;
  res.first = quad(C) - coe[2] - u - w;
  res.second = -1*C*res.first - mod_div(v*w - z*u, w - u);
  res.first = mod(res.first);
  res.second = mod(res.second);
  return res;
}
*/

int_pair addition(int_pair P, int_pair Q) {
  int_pair res;
  if(P == INF) res = Q;
  else if(Q == INF) res = P;
  else if(P != Q) { // if P and Q are points on the curve which are different
    if(P.first == Q.first) res = INF; // if P + Q = 0 then return 0(INf)
    else { // else then use the addition formula
      int u = P.first, v = P.second, w = Q.first, z = Q.second;
      int C = mod_div(z - v, w - u);
      res.first = quad(C) - coe[2] - u - w;
      res.second = -1*C*res.first - mod_div(v*w - z*u, w - u);
      res.first = mod(res.first);
      res.second = mod(res.second);
    }
  }
  else { // else if P and Q are same points in the curve
    if(P.second == 0) res = INF; // if P's y-coordinate is zero, then 2P = 0
    else {// else then use the tangent formula
      int u = P.first, v = P.second;
      int C = mod_div(3*quad(u) + 2*coe[2]*u + coe[1], 2*v);
      res.first = quad(C) - coe[2] - 2*u;
      res.second = -1*C*(res.first) - v + C*u;
      res.first = mod(res.first);
      res.second = mod(res.second);
    }
  }
  return res;
}

int_pair subtraction(int_pair P, int_pair Q) {
  int_pair inv_Q = make_pair(Q.first, mod(-1 * Q.second));
  return addition(P, inv_Q);
}

void crpt1() {
  int_pair p1, p2;
  int m, n;
  cout << "Cryptography 1: " << endl;
  cout << "(All the input should be less than " << MAXN << ")" << endl;
  cout << "Input the information P1(x, y) which A has(in the form of 'x y'): ";
  cin >> p1.first >> p1.second;
  while(points.find(p1) == points.end()) {
    cout << "The input is invalid, please input again: ";
    cin >> p1.first >> p1.second;
  }
  cout << "Input the information P2(x, y) which B has(in the form of 'x y'): ";
  cin >> p2.first >> p2.second;
  while(points.find(p2) == points.end()) {
    cout << "The input is invalid, please input again: ";
    cin >> p2.first >> p2.second;
  }
  cout << "Choose a secret integer m for A: ";
  cin >> m;
  cout << "Choose a secret integer n for B: ";
  cin >> n;
  p1.first = mod(p1.first); p1.second = mod(p1.second);
  p2.first = mod(p2.first); p2.second = mod(p2.second);
  int_pair mp1 = INF, nmp1 = INF, np2 = INF, mnp2 = INF;
  for(int i = 0;i < m;++i) mp1 = addition(mp1, p1); // A calculate mp1 = p1 + ... + p1
  for(int i = 0;i < n;++i) np2 = addition(np2, p2); // B calculate np2 = p1 + ... + p2
  // send mp1 to B and send np2 to A
  for(int i = 0;i < m;++i) mnp2 = addition(mnp2, np2); // A calculate mnp2
  for(int i = 0;i < n;++i) nmp1 = addition(nmp1, mp1); // B calculate nmp1
  if(nmp1 != mnp2) cout << endl << "P1 != P2!!!" << endl << endl;
  else cout << endl << "There is high chance that P1 = P2." << endl << endl;
}

void crpt2() {
  int_pair P, Q;
  int m, n;
  cout << "Cryptography 2: " << endl;
  cout << "(All the input should be less than " << MAXN << ")" << endl;
  cout << "Input the information of P(x, y) (in the form of 'x y'): ";
  cin >> P.first >> P.second;
  while(points.find(P) == points.end()) {
    cout << "The input is invalid, please input again: ";
    cin >> P.first >> P.second;
  }
  cout << "Input the information of Q(x, y) B wants to send(in the form of 'x y'): ";
  cin >> Q.first >> Q.second;
  while(points.find(Q) == points.end()) {
    cout << "The input is invalid, please input again: ";
    cin >> Q.first >> Q.second;
  }
  cout << "Choose a secret integer m for A: ";
  cin >> m;
  cout << "Choose a secret integer n for B: ";
  cin >> n;
  int_pair R = INF, T, S = INF, D;
  for(int i = 0;i < m;++i) R = addition(R, P); // A calculate R = mP
  // A sends R to B
  T = Q;
  for(int i = 0;i < n;++i) T = addition(T, R); // B calculate T = Q + nR
  for(int i = 0;i < n;++i) S = addition(S, P); // B calculate nP
  // B sends nP to A
  D = T;
  for(int i = 0;i < m;++i) D = subtraction(D, S); // A calculate D = T - mS
  // We have T - mS = Q + nR - mnP = Q + nmP - mnP = Q
  printf("\nA has D = T - mS = (%d, %d), which equals to B's Q = (%d, %d)\n", D.first, D.second, Q.first, Q.second);
}

int main() {
  initiate();
  compPoints();
  printPoints();
  crpt1();
  crpt2();
  /* test the addition and subtraction function
    while(1) {
      int a, b, c, d;
      cin >> a >> b >> c >> d;
      if(a == -1) return 0;
      int_pair res = addition(make_pair(a, b), make_pair(c, d));
      cout << res.first << " " << res.second << endl;
      res = subtraction(make_pair(a, b), make_pair(c, d));
      cout << res.first << " " << res.second << endl;
    }
  */
  return 0;
}
