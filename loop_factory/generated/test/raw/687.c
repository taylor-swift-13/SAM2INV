int main1(){
  int wc, q, ub7a, cwix;

  wc=1;
  q=(1%40)+2;
  ub7a=0;
  cwix=0;

  while (q!=ub7a) {
      ub7a = q;
      q = (q+wc/q)/2;
      cwix = cwix + q;
  }

}
