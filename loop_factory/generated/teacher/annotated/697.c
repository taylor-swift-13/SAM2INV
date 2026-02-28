int main1(int k,int m,int n,int p){
  int d, q, g, y, j, u, a;

  d=62;
  q=0;
  g=4;
  y=-4;
  j=3;
  u=d;
  a=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g >= 4;
  loop invariant (g - 4) % 4 == 0;
  loop invariant y <= g;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (g - y) % 4 == 0;
  loop invariant g % 4 == 0;
  loop invariant (k == \at(k, Pre));
  loop invariant (m == \at(m, Pre));
  loop invariant (n == \at(n, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (d == 62);
  loop invariant (j == 3);
  loop invariant ( (y == -4 && g == 4) || (g - y == 4) ) && (g >= 4) && (y <= g);
  loop invariant (k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && u >= 6);
  loop invariant j == 3;
  loop assigns y, g, u;
*/
while (1) {
      y = g;
      g = g+3;
      u = g+y+j;
      g = g+1;
  }

}
