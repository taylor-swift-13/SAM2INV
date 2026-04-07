int main1(){
  int a3, hh3, k, ug, w, l, sl, hl2;

  a3=1+20;
  hh3=0;
  k=hh3;
  ug=1*2;
  w=hh3;
  l=a3;
  sl=a3;
  hl2=-1;

  while (1) {
      if (!(hh3 < a3)) {
          break;
      }
      hh3++;
      k = (k + hh3) % 9;
      ug = (ug + k) % 8;
      w = (w + ug) % 7;
      l = (l + w) % 6;
      hl2 = (hl2 + l) % 4;
      if (k<a3+5) {
          sl = sl + sl;
      }
      if (sl<a3+4) {
          sl = sl + hh3;
      }
      if (!(!(sl+4<a3))) {
          sl = l%10;
      }
  }

}
