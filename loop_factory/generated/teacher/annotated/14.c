int main1(int b,int p){
  int r, t, v;

  r=20;
  t=0;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 20;
  loop invariant t >= 0;
  loop invariant t <= r;
  loop invariant v == t + 8;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == 8 + t;
  loop invariant 0 <= t;
  loop invariant v - t == 8;
  loop assigns v, t;
*/
while (t<r) {
      v = v+1;
      t = t+1;
  }

}
