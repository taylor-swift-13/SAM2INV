int main1(){
  int qsi, rb7p, l0, u6;

  qsi=10;
  rb7p=0;
  l0=4;
  u6=qsi;

  while (1) {
      if (!(rb7p<qsi)) {
          break;
      }
      if (rb7p<qsi/2) {
          l0 = l0 + u6;
      }
      else {
          l0 = l0 + 1;
      }
      rb7p = qsi;
  }

}
