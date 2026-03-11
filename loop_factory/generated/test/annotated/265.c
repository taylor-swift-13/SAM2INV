int main1(){
  int k5z, q5, t, zdt, kqc;
  k5z=(1%26)+14;
  q5=0;
  t=35;
  zdt=1;
  kqc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q5 == kqc;
  loop invariant k5z == 15;
  loop invariant t <= 35;
  loop invariant zdt == kqc + 1;
  loop invariant zdt <= k5z + 1;
  loop invariant 0 <= kqc;
  loop assigns t, kqc, zdt, q5;
*/
while (t>0&&zdt<=k5z) {
      if (!(t<=zdt)) {
          t = 0;
      }
      else {
          t -= zdt;
      }
      kqc++;
      zdt += 1;
      q5++;
  }
}