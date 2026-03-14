int main1(int e){
  int svqd, q, na, j, tf;
  svqd=15;
  q=0;
  na=0;
  j=-2;
  tf=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tf == svqd * na;
  loop invariant 0 <= na;
  loop invariant na <= svqd;
  loop invariant (na <= svqd/2) ==> (j == -2);
  loop invariant (na > svqd/2) ==> (j == -2 + 2 * (na - svqd/2));
  loop assigns na, tf, j;
*/
while (na<svqd) {
      if (!(!(na>=svqd/2))) {
          j += 2;
      }
      tf += svqd;
      na = na + 1;
  }
}