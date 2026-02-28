int main1(int k,int q){
  int v, y, t;

  v=q;
  y=2;
  t=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == q;
  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant y >= 2;
  loop invariant t >= 0;
  loop invariant v == \at(q, Pre) && (t == 1 || t == 2) && y >= 2;

  loop invariant t <= 2;
  loop invariant (t >= 0);
  loop invariant (y >= 2);
  loop invariant 1 <= t <= 2;
  loop assigns t, y;
*/
while (y+1<=v) {
      t = t-t;
      t = t+1;
      y = y+1;
  }

}
