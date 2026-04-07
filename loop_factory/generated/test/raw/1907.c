int main1(){
  int bf, fc0, s, t, d, uk, wv9, ad2, wsnl;

  bf=122;
  fc0=0;
  s=1;
  t=12;
  d=4;
  uk=bf;
  wv9=25;
  ad2=1+3;
  wsnl=0;

  while (fc0 < bf) {
      if ((fc0 % 2) == 0) {
          s++;
          uk += 1;
      }
      else {
          t += 1;
          d += 2;
      }
      fc0 = fc0 + 1;
      if (fc0<t+3) {
          wv9 = wv9 + fc0;
      }
      ad2 += 2;
      wsnl = wsnl + s;
      ad2 += wsnl;
      wsnl += wv9;
  }

}
