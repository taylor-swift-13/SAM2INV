int main1(int b,int m){
  int y, t, v;

  y=m+7;
  t=3;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0 || v == 3;
  loop invariant t >= 3;
  loop invariant (t - 3) % 3 == 0;
  loop invariant y == \at(m, Pre) + 7;
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant t % 3 == 0;
  loop invariant (v == 0 || v == 3) && (v >= 0) && (v <= 3);
  loop invariant t % 3 == 0 && t >= 3 && (v == 0 || (t == 3 && v == 3));
  loop invariant y == \at(m, Pre) + 7 &&
                   m == \at(m, Pre) &&
                   b == \at(b, Pre) &&
                   t >= 3 &&
                   (t - 3) % 3 == 0 &&
                   (v == 0 || v == 3);
  loop invariant t == 3 || t <= y;
  loop invariant y == m + 7;
  loop invariant (t != 3) ==> (v == 0);
  loop assigns t, v;
*/
while (t<=y-3) {
      v = v+t;
      v = v-v;
      t = t+3;
  }

}
