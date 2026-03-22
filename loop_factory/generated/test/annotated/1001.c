int main1(){
  int nc, czn, mreu, jeo, w2;
  nc=1-5;
  czn=nc;
  mreu=20;
  jeo=1;
  w2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w2 == jeo - 1;
  loop invariant czn == nc + w2;
  loop invariant jeo >= 1;
  loop invariant mreu <= 20;
  loop invariant czn == w2 - 4;
  loop assigns mreu, w2, czn, jeo;
*/
while (mreu>0&&jeo<=nc) {
      if (!(mreu<=jeo)) {
          mreu = 0;
      }
      else {
          mreu -= jeo;
      }
      w2++;
      czn++;
      jeo = jeo + 1;
  }
}