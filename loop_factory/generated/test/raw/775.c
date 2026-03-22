int main1(int m){
  int r0, p4, hc, le4a, max;

  r0=m-8;
  p4=r0+5;
  hc=p4;
  le4a=0;
  max=1;

  while (1) {
      if (!(p4>r0)) {
          break;
      }
      hc += p4;
      le4a = le4a*le4a;
      max = max+hc*le4a;
      p4 = p4 - 1;
  }

}
