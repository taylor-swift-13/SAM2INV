int main1(){
  int jsgp, j, i, kdi;
  jsgp=18;
  j=0;
  i=0;
  kdi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= j;
  loop invariant j <= jsgp;
  loop invariant (j <= jsgp/2) ==> (kdi == 0);
  loop invariant kdi >= 0;
  loop invariant (j < jsgp/2 ==> i == 0) && (j >= jsgp/2 ==> i == 4 * (j - jsgp/2));
  loop assigns i, j, kdi;
*/
while (j<jsgp) {
      if (j>=jsgp/2) {
          i += 4;
      }
      kdi = kdi + i;
      j++;
  }
}