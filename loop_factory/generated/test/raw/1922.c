int main1(){
  int ku8, o, l9, wv, m, izr, fg, p5;

  ku8=1-4;
  o=ku8;
  l9=14;
  wv=0;
  m=o;
  izr=0;
  fg=o;
  p5=0;

  while (o<ku8) {
      if (o%2==0) {
          if (l9>0) {
              l9--;
              wv = wv + 1;
          }
      }
      else {
          if (wv>0) {
              wv--;
              l9 = l9 + 1;
          }
      }
      m++;
      izr = izr + l9;
      o = o + 1;
      p5 = m+izr+fg;
      m++;
  }

}
