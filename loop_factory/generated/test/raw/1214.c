int main1(){
  int pv, r4, m, r8ia, i62;

  pv=36;
  r4=0;
  m=1;
  r8ia=6;
  i62=0;

  while (1) {
      if (!(i62<=pv)) {
          break;
      }
      r4 = r4 + m;
      i62 += 1;
      m += r8ia;
      r8ia += 2;
      r4 = r4*3;
      m = m/3;
  }

}
