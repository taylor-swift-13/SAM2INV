int main1(int p,int q){
  int r, t, e, v;

  r=(q%6)+8;
  t=1;
  e=r;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (\at(q,Pre) % 6) + 8;
  loop invariant 1 <= t <= r;
  loop invariant e == r + 3*(t - 1);
  loop invariant v == 3*t - 2;
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant t >= 1;
  loop invariant t <= r;
  loop invariant 1 <= t;
  loop invariant r == (q % 6) + 8;
  loop assigns e, v, t;
*/
while (t<=r-1) {
      e = e+3;
      v = v+2;
      if (t<e+5) {
          v = v+1;
      }
      else {
          v = v+r;
      }
      t = t+1;
  }

}
