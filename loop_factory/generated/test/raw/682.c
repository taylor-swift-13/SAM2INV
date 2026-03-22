int main1(int x){
  int pms2, pclm, hf3, ssa;

  pms2=40;
  pclm=0;
  hf3=(x%40)+2;
  ssa=0;

  while (1) {
      if (!(hf3!=ssa)) {
          break;
      }
      ssa = hf3;
      hf3 = (hf3+pms2/hf3)/2;
      x += pclm;
  }

}
