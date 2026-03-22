int main1(){
  int zh, bt, m41, mui, j1, c4;

  zh=1+14;
  bt=zh+7;
  m41=bt;
  mui=-2;
  j1=bt;
  c4=(1%6)+2;

  while (1) {
      if (!(j1<zh)) {
          break;
      }
      mui = mui*c4;
      m41 = m41*c4+2;
      j1 += 1;
      c4 = c4 + mui;
      c4 = c4*c4;
  }

}
