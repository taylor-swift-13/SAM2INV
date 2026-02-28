int main1(int a,int b,int p,int q){
  int r, d, v, t, m, z, g, o;

  r=(b%27)+8;
  d=0;
  v=r;
  t=-4;
  m=5;
  z=-2;
  g=1;
  o=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d >= 0;

  loop invariant v == r + 4*d;
  loop invariant m == 5 + 2*d;

  loop invariant r == (b % 27) + 8;
  loop invariant v - 4*d == (\at(b, Pre) % 27) + 8;
  loop invariant m - 2*d == 5;
  loop invariant r == (\at(b, Pre) % 27) + 8;
  loop assigns v, d, m;
*/
while (1) {
      if (d>=r) {
          break;
      }
      v = v+1;
      d = d+1;
      v = v+3;
      m = m+2;
  }

}
