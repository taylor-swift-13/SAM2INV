int main1(){
  int lr9, pf1c, vz;
  lr9=1*4;
  pf1c=0;
  vz=pf1c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vz == 4 * pf1c;
  loop invariant pf1c <= lr9;
  loop invariant pf1c >= 0;
  loop assigns vz, pf1c;
*/
while (1) {
      vz += 4;
      pf1c += 1;
      if (pf1c>=lr9) {
          break;
      }
  }
}