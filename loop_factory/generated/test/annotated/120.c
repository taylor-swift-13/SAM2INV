int main1(int i,int x){
  int ku, z3, kt;
  ku=34;
  z3=0;
  kt=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ku == 34;
  loop invariant x == \at(x, Pre);
  loop invariant 0 <= z3;
  loop invariant z3 <= ku;
  loop invariant kt >= 1 && (kt % 2 == 0 || kt == 1);
  loop invariant kt <= 22;
  loop invariant kt == 1 || kt == 2;
  loop invariant i == \at(i, Pre) + 2*z3;
  loop assigns kt, z3, i;
*/
while (z3<ku) {
      if (kt>=12) {
          kt = -1;
      }
      if (kt<=2) {
          kt = 1;
      }
      kt = kt + kt;
      z3 += 1;
      i = i + kt;
  }
}