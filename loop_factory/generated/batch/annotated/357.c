int main1(int p,int q){
  int r, t, e, v;

  r=(q%6)+8;
  t=1;
  e=r;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre) &&
                   q == \at(q, Pre) &&
                   r == (\at(q, Pre) % 6) + 8;
  loop invariant e == r + t - 1 &&
                   v == 2*t - 1 &&
                   t <= r;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == ((\at(q, Pre) % 6) + 8);
  loop invariant e == r + t - 1;
  loop invariant v == 2*t - 1;
  loop invariant t <= r;
  loop invariant p == \at(p, Pre) &&
                   q == \at(q, Pre) &&
                   r == (\at(q, Pre) % 6) + 8 &&
                   t >= 1 && t <= r;
  loop invariant e - t == (\at(q, Pre) % 6) + 7 &&
                   v == 2*t - 1;
  loop invariant e - t == (q % 6) + 7;
  loop invariant 1 <= t;
  loop invariant e - t == r - 1;
  loop invariant r == (q % 6) + 8;
  loop assigns e, v, t;
*/
while (t<=r-1) {
      e = e+1;
      v = v-1;
      v = v+3;
      t = t+1;
  }

}
