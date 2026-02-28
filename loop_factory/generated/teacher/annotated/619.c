int main1(int k,int n){
  int q, u, x, p;

  q=n;
  u=0;
  x=-2;
  p=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == n;
  loop invariant (x + 2) % 7 == 0;
  loop invariant x >= -2;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (n <= 3) ==> (p <= 2*x + 7);
  loop invariant ((x == -2 && p == n) || (p == 2*x - 7));
  loop invariant (x == -2 && p == n) || (p == 2*x - 7);
  loop assigns p, x;
*/
while (1) {
      p = x;
      x = x+2;
      x = x+5;
      p = p+x;
  }

}
