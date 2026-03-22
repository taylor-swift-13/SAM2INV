int main1(int r){
  int c8, xe, xuz, e06;
  c8=51;
  xe=c8;
  xuz=4;
  e06=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e06 == xuz * (c8 - xe);
  loop invariant xe >= 0;
  loop invariant xe <= c8;
  loop assigns e06, xe;
*/
while (1) {
      if (!(xe>0)) {
          break;
      }
      e06 = e06+xuz*xe;
      xe = 0;
  }
}