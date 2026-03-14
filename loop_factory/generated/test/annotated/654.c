int main1(){
  int c1ot, vzs, et, yabm, e;
  c1ot=1;
  vzs=c1ot;
  et=1;
  yabm=0;
  e=vzs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yabm == (et - 1) * et * (2 * et - 1) / 6;
  loop invariant e == 1 + c1ot*(et - 1);
  loop assigns yabm, et, e;
*/
while (1) {
      if (!(et<=c1ot)) {
          break;
      }
      yabm = yabm+et*et;
      et++;
      e = e + c1ot;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (c1ot - 1) % 7 == 0;
  loop invariant 1 <= c1ot;
  loop assigns c1ot;
*/
for (; c1ot<e; c1ot = c1ot + 7) {
  }
}