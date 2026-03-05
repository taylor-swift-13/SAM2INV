int main1(int x){
  int dn, lj, kwp, wy;
  dn=x+19;
  lj=0;
  kwp=0;
  wy=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kwp == lj % 2;
  loop invariant wy == 11 - (lj % 2);
  loop invariant dn == \at(x, Pre) + 19;
  loop invariant x == \at(x, Pre) + dn * lj;
  loop invariant 0 <= lj;
  loop invariant lj <= dn || dn <= 0;
  loop assigns lj, wy, kwp, x;
*/
while (lj<dn) {
      if (kwp==0) {
          kwp += 1;
          wy--;
          kwp = 1;
      }
      else {
          kwp = kwp - 1;
          wy = wy + 1;
          kwp = 0;
      }
      lj++;
      x += dn;
  }
}