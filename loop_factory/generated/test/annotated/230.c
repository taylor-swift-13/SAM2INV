int main1(){
  int zp, zu;
  zp=(1%29)+20;
  zu=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zu == 0 || zu == 2 || zu == 4;
  loop invariant zp == 21;
  loop assigns zu;
*/
while (zu<zp) {
      zu = (zu+1)%4;
      zu += 1;
  }
}