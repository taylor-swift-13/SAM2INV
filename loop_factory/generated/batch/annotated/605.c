int main1(int b,int n){
  int y, t, c, v;

  y=11;
  t=0;
  c=-3;
  v=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant t % 5 == 0;
  loop invariant 0 <= t;
  loop invariant t <= y;
  loop invariant c <= -3;

  loop invariant (v - 2) % 3 == 0;
  loop invariant y == 11;
  loop invariant c < 0;
  loop invariant c % 3 == 0;
  loop invariant -1 <= v;
  loop invariant v <= 11;
  loop assigns c, v, t;
*/
while (t+5<=y) {
      c = c*2;
      v = v+c;
      v = v%3;
      if (y*y<=y+6) {
          v = v*2;
      }
      t = t+5;
  }

}
