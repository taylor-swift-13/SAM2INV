int main1(int i,int l){
  int z75, a1, otk, t95;
  z75=l;
  a1=0;
  otk=0;
  t95=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z75 == l;
  loop invariant t95 >= 0;
  loop invariant otk == 5*a1 - a1*(a1 - 1)/2;
  loop invariant i == \at(i,Pre) + a1 * z75;
  loop invariant t95 == 5 - a1;
  loop assigns a1, otk, t95, i;
*/
while (a1<z75&&t95>0) {
      a1 += 1;
      otk += t95;
      t95 -= 1;
      i += z75;
  }
}