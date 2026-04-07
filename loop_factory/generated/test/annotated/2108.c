int main1(int z){
  int lso9, d7, ng, rh, oi;
  lso9=z;
  d7=0;
  ng=0;
  rh=d7;
  oi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oi == 3 * d7;
  loop invariant ng == 0;
  loop invariant rh == 0;
  loop invariant d7 >= 0;
  loop invariant (lso9 >= 0) ==> (d7 <= lso9);
  loop invariant lso9 == \at(z, Pre);
  loop assigns d7, oi, ng;
*/
while (d7 < lso9) {
      d7 += 1;
      oi = oi + 3;
      ng = ng+ng-rh;
  }
}