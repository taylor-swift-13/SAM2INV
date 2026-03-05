int main1(int r,int i){
  int w, t;
  w=75;
  t=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t - 1) % 3 == 0;
  loop invariant t >= 1;
  loop invariant t <= w + 2;
  loop invariant i == \at(i, Pre);
  loop invariant r == \at(r, Pre);
  loop invariant w == 75;
  loop assigns t;
*/
while (t<w) {
      t = t + 3;
  }
}