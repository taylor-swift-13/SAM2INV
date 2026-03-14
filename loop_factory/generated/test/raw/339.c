int main1(){
  int mra, s, pw, aq, uirq;

  mra=0;
  s=(1%18)+5;
  pw=(1%15)+3;
  aq=s;
  uirq=mra;

  while (1) {
      if (!(s!=0)) {
          break;
      }
      s -= 1;
      pw--;
      aq = aq + s;
  }

  while (uirq<=mra-1) {
      s++;
      uirq += 1;
      aq = aq + uirq;
  }

}
