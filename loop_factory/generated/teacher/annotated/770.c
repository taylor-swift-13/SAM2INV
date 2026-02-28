int main1(int a,int b,int n,int q){
  int r, g, v, p, z, u;

  r=(a%29)+7;
  g=0;
  v=6;
  p=b;
  z=b;
  u=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - g == 6;
  loop invariant p == \at(b, Pre);
  loop invariant z == \at(b, Pre);
  loop invariant g >= 0;
  loop invariant g >= 1 ==> u == v + p + z - 1;
  loop invariant g == v - 6;
  loop invariant v >= 6;

  loop invariant p == z;

  loop invariant v == g + 6;
  loop invariant r == (\at(a, Pre) % 29) + 7;
  loop invariant (g > 0) ==> (u == v + p + z - 1);
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns u, v, g;
*/
while (1) {
      u = v+p+z;
      v = v+1;
      g = g+1;
  }

}
