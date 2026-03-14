int main1(int y){
  int s4, xt, v0, xu, aly;
  s4=y+18;
  xt=s4;
  v0=0;
  xu=0;
  aly=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v0 >= 0;
  loop invariant aly == 4 - v0;
  loop invariant y == \at(y,Pre) + v0 * xt;
  loop invariant v0 <= 4;
  loop invariant xu == (v0 * (9 - v0)) / 2;
  loop assigns xu, v0, y, aly;
*/
while (v0<s4&&aly>0) {
      xu += aly;
      v0++;
      y += xt;
      aly = aly - 1;
  }
}