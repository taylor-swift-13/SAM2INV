int main1(){
  int q6, lm, bz, uqx, dk4, m, pq9;

  q6=(1%15)+12;
  lm=q6;
  bz=(1%60)+60;
  uqx=(1%9)+2;
  dk4=0;
  m=0;
  pq9=0;

  while (1) {
      if (bz<=uqx*dk4+m) {
          break;
      }
      if (m==uqx-1) {
          m = 0;
          dk4++;
      }
      else {
          m++;
      }
      pq9 = pq9 + lm;
  }

}
