int main1(int y,int z){
  int t, lv2, sr, e;
  t=52;
  lv2=t;
  sr=0;
  e=lv2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 52;
  loop invariant (sr % 3) == 0;
  loop invariant 6*(z - \at(z, Pre)) == 2*t*sr - sr*sr + 3*sr;
  loop invariant (sr == 0) ==> (e == t);
  loop invariant (sr != 0) ==> (e == t - sr + 3);
  loop invariant 0 <= sr;
  loop assigns z, sr, e;
*/
while (sr<t) {
      e = t-sr;
      z = z + e;
      sr = sr + 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 52;
  loop invariant lv2 >= 52;
  loop invariant sr >= 0;
  loop assigns lv2, e, y;
*/
while (lv2<=sr-1) {
      lv2 = lv2 + 1;
      e = sr-lv2;
      y = y + e;
  }
}