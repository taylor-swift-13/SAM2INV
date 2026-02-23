int main1(int p){
  int h, t, b, x;

  h=22;
  t=4;
  b=-8;
  x=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t - b == 12;
  loop invariant t <= h;
  loop invariant t >= 4;
  loop invariant p == \at(p, Pre);
  loop invariant b - t == -12;
  loop invariant 4 <= t;
  loop invariant h == 22;
  loop invariant b == t - 12;
  loop assigns b, t;
*/
while (t<=h-1) {
      b = b+1;
      t = t+1;
  }

}
