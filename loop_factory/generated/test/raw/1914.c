int main1(){
  int a61, sjo9, ek, v, w92h, e, vc, ninj;

  a61=(1%6)+12;
  sjo9=0;
  ek=14;
  v=18;
  w92h=0;
  e=6;
  vc=0;
  ninj=-2;

  while (sjo9<a61) {
      if (!(w92h!=0)) {
          ek = ek - 3;
          v = v + 3;
          w92h = 0;
      }
      else {
          ek = ek + 3;
          v = v - 3;
          w92h = 1;
      }
      sjo9 += 1;
      if (ek<w92h+5) {
          e += 1;
      }
      ninj += ek;
      vc += v;
      e = e+vc+ninj;
  }

}
