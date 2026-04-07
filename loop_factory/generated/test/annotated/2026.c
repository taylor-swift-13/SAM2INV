int main1(){
  int jjd, ls, lm, rv56, m, bxlp;
  jjd=72;
  ls=0;
  lm=0;
  rv56=0;
  m=6;
  bxlp=ls;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 6 + 2 * lm;
  loop invariant bxlp == (lm + 1) * ls;
  loop invariant (lm == 0 && rv56 == 0) || rv56 == jjd - lm;
  loop invariant (bxlp == ls * lm);
  loop invariant (0 <= lm && lm <= jjd);
  loop invariant (0 <= rv56 && rv56 <= jjd);
  loop assigns lm, rv56, bxlp, m;
*/
while (1) {
      if (!(lm<jjd)) {
          break;
      }
      lm++;
      rv56 = jjd-lm;
      bxlp = bxlp + ls;
      m += 2;
  }
}