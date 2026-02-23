int main1(int n){
  int y, t, v, e;

  y=15;
  t=0;
  v=5;
  e=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 5*v - 25;
  loop invariant 0 <= t;

  loop invariant n == \at(n, Pre);
  loop invariant y == 15;
  loop invariant e + v == 7;
  loop invariant v >= 5;
  loop invariant v + e == 7;
  loop invariant t == 5 * (v - 5);
  loop invariant t <= y;
  loop invariant t >= 0;
  loop invariant 5 * (v - 5) == t;
  loop assigns v, e, t;
*/
while (t<=y-5) {
      v = v+1;
      e = e-1;
      t = t+5;
  }

}
