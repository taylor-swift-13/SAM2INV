int main1(){
  int uyo1, fhpy, hl, k5ye, jn;
  uyo1=8;
  fhpy=uyo1;
  hl=uyo1 - 1;
  k5ye=uyo1;
  jn=uyo1 - 2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k5ye == fhpy;
  loop invariant jn == (k5ye - 2);
  loop invariant 0 <= fhpy;
  loop invariant fhpy <= uyo1;
  loop invariant (fhpy == uyo1 && hl == (uyo1 - 1)) || hl == (2 * k5ye - 3);
  loop invariant ((fhpy == uyo1) ==> (hl == uyo1 - 1));
  loop invariant ((fhpy < uyo1) ==> (hl == 2 * k5ye - 3));
  loop invariant ( (fhpy == uyo1 && hl == uyo1 - 1)
                     || (fhpy < uyo1 && hl == 2 * k5ye - 3) );
  loop assigns k5ye, fhpy, jn, hl;
*/
while (fhpy > 0) {
      k5ye -= 1;
      fhpy -= 1;
      jn = (hl = k5ye - 1, k5ye - 2);
      hl += jn;
  }
}