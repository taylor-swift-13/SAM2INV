int main1(int m){
  int qt, p, hsi, rws;

  qt=(m%28)+13;
  p=qt;
  hsi=(m%20)+10;
  rws=(m%15)+8;

  while (1) {
      if (!(hsi>0&&rws>0)) {
          break;
      }
      if (!(!(p%2==0))) {
          hsi--;
      }
      else {
          rws--;
      }
      p++;
  }

}
