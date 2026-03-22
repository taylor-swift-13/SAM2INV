int main1(){
  int gw, ym, iaq, l7, ep, vh, tfp;

  gw=51;
  ym=0;
  iaq=8;
  l7=8;
  ep=0;
  vh=8;
  tfp=0;

  while (ym<=gw-1) {
      if (!(!(ym%3==0))) {
          if (iaq>0) {
              iaq--;
              ep = ep + 1;
          }
      }
      else {
          if (iaq<vh) {
              iaq = iaq + 1;
              l7++;
          }
      }
      tfp = tfp + 1;
      ym += 1;
  }

}
