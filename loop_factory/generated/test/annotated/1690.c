int main1(){
  int lbqv, xv, jn;
  lbqv=39;
  xv=lbqv;
  jn=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lbqv == 39;
  loop invariant ((xv == lbqv) || (xv == 0));
  loop invariant (jn <= lbqv) && ((jn == lbqv) || ((jn - 1) % 3 == 0));
  loop invariant 1 <= jn <= lbqv;
  loop invariant 0 <= xv <= lbqv;
  loop assigns jn, xv;
*/
while (xv>=1) {
      if (jn+3<=lbqv) {
          jn = jn + 3;
      }
      else {
          jn = lbqv;
      }
      xv = 0;
  }
}