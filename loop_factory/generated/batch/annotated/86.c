int main1(int a,int b){
  int v, t, y;

  v=62;
  t=0;
  y=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 62 && t % 4 == 0 && 0 <= t;
  loop invariant y >= b;
  loop invariant t % 4 == 0;
  loop invariant t >= 0;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre) && v == 62;
  loop invariant (0 <= t) && (t <= 64);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant 0 <= t && v == 62 && y >= \at(b, Pre);
  loop assigns y, t;
*/
while (t<v) {
      y = y+t;
      if (t+4<=a+v) {
          y = y+1;
      }
      t = t+4;
  }

}
