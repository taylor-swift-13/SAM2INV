int main1(){
  int k, izh, hw, ji, qle8, e;

  k=(1%34)+14;
  izh=0;
  hw=izh;
  ji=0;
  qle8=0;
  e=(1%6)+2;

  while (1) {
      if (qle8>=k) {
          break;
      }
      ji = ji*e;
      qle8 = qle8 + 1;
      hw = hw*e+1;
      e = e+(ji%6);
  }

}
