int main1(int n,int p){
  int f, t, g;

  f=71;
  t=f;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == p + (f - t) * (f + t + 1) / 2;
  loop invariant 0 <= t && t <= f;
  loop invariant g >= p;
  loop invariant f == 71;
  loop invariant (0 <= t) && (t <= 71);
  loop invariant 2*(g - p) == 5112 - t*t - t;
  loop invariant p == \at(p, Pre) && n == \at(n, Pre);
  loop invariant g == \at(p, Pre) + 2556 - (t * (t + 1)) / 2;
  loop invariant 0 <= t && t <= 71;
  loop invariant t >= 0;
  loop invariant t <= f;
  loop invariant g + t*(t+1)/2 == \at(p, Pre) + f*(f+1)/2;
  loop invariant g == p + 2556 - t*(t+1)/2;
  loop invariant t <= 71;
  loop assigns g, t;
*/
while (t>0) {
      g = g+t;
      t = t-1;
  }

}
