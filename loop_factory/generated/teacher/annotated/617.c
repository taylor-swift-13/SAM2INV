int main1(int k,int m){
  int g, i, v, e, y, n;

  g=73;
  i=1;
  v=8;
  e=-4;
  y=2;
  n=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant y == 2*n + 10;
  loop invariant e == (n + 4) * (n + 5) - 4;

  loop invariant g == 73;
  loop invariant e == n*n + 9*n + 16;
  loop invariant n <= g + 1;
  loop invariant 3*v == n*n*n + 12*n*n + 35*n + 36;
  loop invariant 3*v == 24 + (n+4)*(n*n + 8*n + 3);
  loop invariant -4 <= n;
  loop assigns v, e, y, n;
*/
while (n<=g) {
      v = v+e;
      e = e+y;
      y = y+2;
      n = n+1;
  }

}
