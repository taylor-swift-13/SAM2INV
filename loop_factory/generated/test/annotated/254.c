int main1(){
  int vfo, t64o, t, y2d;
  vfo=8;
  t64o=vfo;
  t=vfo;
  y2d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t64o >= 8;
  loop invariant vfo == 8;
  loop invariant y2d == 0;
  loop invariant t == t64o;
  loop assigns t, t64o;
*/
while (t64o-1>=0) {
      if (t64o<vfo/2) {
          t = t + y2d;
      }
      else {
          t += 1;
      }
      t64o = t64o + 1;
  }
}