int main1(int w){
  int gu, vv5z, y6g, pv;
  gu=w*3;
  vv5z=0;
  y6g=0;
  pv=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gu == 3 * \at(w, Pre);
  loop invariant y6g >= 0;
  loop invariant (gu >= 0 ==> y6g <= gu);
  loop invariant w == \at(w, Pre) + ((y6g * (y6g + 1)) / 2);
  loop invariant (y6g == 0 && pv == -4) || pv == (gu - (y6g - 1));
  loop assigns pv, y6g, w;
*/
while (y6g<gu) {
      pv = gu-y6g;
      y6g += 1;
      w += y6g;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gu == \at(w, Pre) * 3;
  loop invariant (gu >= 0 ==> vv5z <= gu);
  loop invariant 0 <= vv5z;
  loop assigns vv5z;
*/
while (1) {
      vv5z = vv5z + 1;
      if (vv5z>=gu) {
          break;
      }
  }
/*@
  assert (gu == 3 * \at(w, Pre));
*/

}