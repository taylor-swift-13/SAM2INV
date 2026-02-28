int main1(int a,int b,int m,int p){
  int r, t, g, v;

  r=m-7;
  t=r;
  g=t;
  v=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(m, Pre) - 7;
  loop invariant v == \at(m, Pre) - 7;
  loop invariant t <= r;
  loop invariant g - (2 + 2*v) * t == -(\at(m, Pre) - 7) - 2 * (\at(m, Pre) - 7) * (\at(m, Pre) - 7);
  loop invariant g - 2*(r+1)*t == -2*r*r - r;
  loop invariant v == r;
  loop invariant r == m - 7;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant g >= t;
  loop invariant g - (2*v + 2)*(t - r) == r;
  loop invariant g == r + 2*(r+1)*(t - r);
  loop invariant g >= r;
  loop assigns g, t;
*/
while (1) {
      if (t>=r) {
          break;
      }
      g = g+1;
      t = t+1;
      g = g+v+v;
      g = g+1;
  }

}
