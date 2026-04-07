int main1(){
  int h, emy, t3, h3, xs;

  h=1;
  emy=0;
  t3=0;
  h3=0;
  xs=0;

  while (1) {
      if (!(emy < h)) {
          break;
      }
      xs = xs + emy*emy*emy;
      emy++;
      h3 += h;
      t3 = t3+h3+h3;
  }

}
