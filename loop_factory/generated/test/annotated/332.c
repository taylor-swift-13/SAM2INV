int main1(){
  int wjs, cy, uu, tm7q;
  wjs=11;
  cy=0;
  uu=0;
  tm7q=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tm7q == cy + 1;
  loop invariant uu >= 0;
  loop invariant 0 <= cy <= wjs;
  loop invariant 1 <= tm7q <= wjs + 1;
  loop invariant uu <= tm7q;
  loop assigns uu, tm7q, cy;
*/
while (uu>0&&tm7q<=wjs) {
      if (uu>tm7q) {
          uu = uu - tm7q;
      }
      else {
          uu = 0;
      }
      uu = uu + 1;
      tm7q = tm7q + 1;
      cy++;
  }
}