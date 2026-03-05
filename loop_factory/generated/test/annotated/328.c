int main1(int m){
  int r9, ggt;
  r9=m-1;
  ggt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r9 == \at(m, Pre) - 1;
  loop invariant r9 == 0 ==> m == \at(m, Pre);
  loop invariant ggt == 0;
  loop invariant r9 != 0 ==> (m - \at(m, Pre)) % r9 == 0;
  loop assigns ggt, m;
*/
while (ggt!=ggt) {
      ggt = ggt;
      ggt = (ggt+r9/ggt)/2;
      m = m + r9;
  }
}