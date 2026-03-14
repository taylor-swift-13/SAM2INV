int main1(){
  int b92, tp, s8, em, s4;

  b92=68;
  tp=0;
  s8=(1%28)+10;
  em=5;
  s4=b92;

  while (s8>tp) {
      s8 -= tp;
      tp = tp + 1;
      s4 = s4+(s8%8);
      em = em+(tp%7);
  }

  while (1) {
      b92++;
      if (b92>=tp) {
          break;
      }
  }

}
