int main1(){
  int z55, haj, fy, k, lp, c;
  z55=59;
  haj=1;
  fy=0;
  k=20;
  lp=haj;
  c=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lp == haj * fy + 1;
  loop invariant 0 <= fy <= z55;
  loop invariant lp - 1 == fy;
  loop invariant (fy == 0) ==> (k == 20);
  loop invariant (fy > 0) ==> (k == fy - 1);
  loop invariant k <= z55 - 1;
  loop assigns k, lp, fy;
*/
while (fy<z55) {
      k = fy;
      lp = lp + haj;
      fy++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lp - c*fy == -235;
  loop invariant 0 <= fy <= z55;
  loop assigns z55, lp, fy;
*/
while (z55<=c-1) {
      z55 = z55 + 1;
      lp = lp + c;
      fy++;
  }
}