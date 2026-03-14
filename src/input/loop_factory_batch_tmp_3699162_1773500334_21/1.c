int main1(int k){
  int lp, wt, q, hhq, ivbm, w;

  lp=k+8;
  wt=0;
  q=0;
  hhq=0;
  ivbm=wt;
  w=1;

  while (1) {
      if (!(hhq<lp)) {
          break;
      }
      hhq = hhq + 1;
      q = q + k;
      w += lp;
  }

  while (w<hhq) {
      w += 1;
      lp = lp + k;
      ivbm = ivbm + hhq;
  }

}
