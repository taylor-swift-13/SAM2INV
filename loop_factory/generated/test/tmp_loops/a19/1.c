int main1(){
  int l74a, p5, nq, jyp;

  l74a=1;
  p5=0;
  nq=3;
  jyp=0;

  while (p5<l74a) {
      jyp = p5%5;
      if (p5>=nq) {
          nq = (p5-nq)%5;
          nq = nq+jyp-nq;
      }
      else {
          nq = nq + jyp;
      }
      p5 = p5 + 1;
      nq++;
  }

}
