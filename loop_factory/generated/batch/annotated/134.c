int main1(int p){
  int j, y, t, v;

  j=8;
  y=j;
  t=y;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant j == 8;
  loop invariant t == j || t == j + 2;
  loop invariant y == 8;
  loop invariant t <= j + 2;
  loop invariant t == 8 || t == 10;
  loop invariant j <= t;
  loop invariant y >= 0;
  loop invariant (t == j) || (t == j + 2);
  loop invariant t >= j;
  loop assigns t;
*/
while (y-1>=0) {
      if (t+3<=j) {
          t = t+3;
      }
      else {
          t = j;
      }
      t = t+2;
  }

}
