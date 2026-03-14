int main1(){
  int ms, k, yd, hw, yw, e;

  ms=1;
  k=0;
  yd=0;
  hw=0;
  yw=6;
  e=ms;

  while (1) {
      if (!(yd<ms&&yw>0)) {
          break;
      }
      hw += yw;
      yd += 1;
      e = e + k;
      yw--;
  }

}
