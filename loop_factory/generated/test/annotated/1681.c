int main1(int y){
  int jk, ozht, e1p, ecp;
  jk=102;
  ozht=0;
  e1p=1;
  ecp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e1p == 1 + ozht * jk;
  loop invariant ecp == ozht % 2;
  loop invariant 0 <= ozht;
  loop invariant ozht <= jk;
  loop assigns e1p, ecp, ozht;
*/
while (ozht < jk) {
      e1p = e1p + jk;
      ecp = 1 - ecp;
      ozht = ozht + 1;
  }
}