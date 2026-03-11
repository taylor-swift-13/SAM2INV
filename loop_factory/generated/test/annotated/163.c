int main1(int t,int n){
  int q8, e9, wm, an0v, vr5y;
  q8=t;
  e9=q8;
  wm=0;
  an0v=1;
  vr5y=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= an0v <= 11;
  loop invariant wm >= 0;
  loop invariant q8 == t;
  loop invariant e9 == t + 12 * wm + an0v - 1;
  loop invariant vr5y == e9 - t - 1;
  loop invariant (e9 >= \at(t, Pre));
  loop invariant q8 == \at(t, Pre);
  loop assigns an0v, vr5y, wm, e9;
*/
while (e9<q8) {
      an0v++;
      vr5y++;
      if (an0v>=12) {
          an0v = an0v - 12;
          wm = wm + 1;
      }
      e9 += 1;
  }
}