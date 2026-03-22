int main1(){
  int p, u2, uc64, jzn, rk;

  p=(1%25)+17;
  u2=0;
  uc64=1;
  jzn=6;
  rk=0;

  while (rk<=p) {
      rk += 1;
      u2 += uc64;
      uc64 += jzn;
      u2 = u2*3;
      jzn += 6;
      uc64 = uc64/3;
  }

}
