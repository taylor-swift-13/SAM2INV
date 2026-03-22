int main1(){
  int p, u2, uc64, jzn, rk;
  p=(1%25)+17;
  u2=0;
  uc64=1;
  jzn=6;
  rk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jzn == 6*(rk + 1);
  loop invariant p == (1 % 25) + 17;
  loop invariant u2 >= 0;
  loop invariant uc64 >= 0;
  loop invariant 0 <= rk <= p + 1;
  loop invariant u2 % 3 == 0;
  loop assigns rk, u2, uc64, jzn;
*/
while (rk<=p) {
      rk += 1;
      u2 += uc64;
      uc64 += jzn;
      u2 = u2*3;
      jzn += 6;
      uc64 = uc64/3;
  }
}