int main1(int a,int b,int m,int q){
  int p, d, t, f, x;

  p=58;
  d=0;
  t=b;
  f=p;
  x=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t - 2*f == b - 2*p;
  loop invariant t >= b;
  loop invariant f >= p;
  loop invariant (t - b) % 10 == 0;
  loop invariant (f - p) % 5 == 0;
  loop invariant p == 58;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant f >= 58;
  loop invariant t - b == 2*(f - 58);
  loop invariant t - 2*f == \at(b, Pre) - 116;
  loop invariant t >= \at(b, Pre);
  loop invariant t - b == 2*(f - p);
  loop assigns t, f;
*/
while (1) {
      t = t+5;
      f = f+5;
      t = t+5;
  }

}
