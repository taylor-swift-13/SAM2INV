int main1(){
  int ze, wr4, nrz;
  ze=1-2;
  wr4=0;
  nrz=ze;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nrz == ze;
  loop invariant wr4 >= ze;
  loop assigns nrz, wr4;
*/
while (wr4<=ze-1) {
      if (!(!(nrz+6<=ze))) {
          nrz += 6;
      }
      else {
          nrz = ze;
      }
      wr4 = ze;
  }
}