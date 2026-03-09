int main1(){
  int vy, c73, l12, y, fe, hs;
  vy=1*2;
  c73=0;
  l12=0;
  y=11;
  fe=c73;
  hs=vy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vy == 2;
  loop invariant hs == vy;
  loop invariant fe == 0;
  loop invariant y == 11 + (l12*(l12+1))/2 - l12*fe;
  loop invariant 0 <= l12;
  loop invariant l12 <= vy;
  loop assigns l12, fe, y;
*/
while (1) {
      if (!(l12<vy)) {
          break;
      }
      l12 = l12 + 1;
      if (hs<=fe) {
          fe = hs;
      }
      y = y+l12-fe;
  }
}