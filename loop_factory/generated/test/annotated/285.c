int main1(int p){
  int jju8, yl, zf;
  jju8=45;
  yl=0;
  zf=yl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zf == 2 * p * (yl / 7);
  loop invariant (yl % 7) == 0;
  loop invariant 0 <= yl;
  loop invariant jju8 == 45;
  loop assigns zf, yl;
*/
while (1) {
      if (!(yl<jju8)) {
          break;
      }
      zf = zf+p+p;
      yl = yl + 7;
  }
}