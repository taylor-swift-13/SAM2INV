int main1(){
  int ebsn, kzu, cd8, dj;
  ebsn=1+16;
  kzu=0;
  cd8=0;
  dj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= cd8 <= ebsn;
  loop invariant kzu == cd8 % 3;
  loop invariant dj == cd8*(cd8+1)/2;
  loop assigns kzu, cd8, dj;
*/
while (cd8<ebsn) {
      kzu = (kzu+1)%3;
      cd8 = cd8 + 1;
      dj = dj + cd8;
  }
}