int main1(){
  int nq, ls6, cz;
  nq=1*2;
  ls6=0;
  cz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ls6;
  loop invariant ls6 <= nq;
  loop invariant cz >= 22 * ls6;
  loop invariant nq == 2;
  loop invariant cz % 22 == 0;
  loop assigns cz, ls6;
*/
while (1) {
      if (!(ls6<nq)) {
          break;
      }
      cz += 11;
      ls6++;
      cz = cz + cz;
  }
}