int main1(){
  int xmt, d5e, zbp, cpd, tgk;
  xmt=(1%40)+9;
  d5e=0;
  zbp=0;
  cpd=0;
  tgk=d5e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tgk == cpd * (xmt + 1);
  loop invariant zbp == cpd % 7;
  loop invariant 0 <= cpd <= xmt;
  loop assigns cpd, tgk, zbp;
*/
while (cpd<xmt) {
      tgk = tgk + xmt;
      cpd += 1;
      zbp = (zbp+1)%7;
      tgk += 1;
  }
}