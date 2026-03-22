int main1(int i){
  int t, o, bjr, h, qsv, xw, c2, k;

  t=67;
  o=0;
  bjr=0;
  h=o;
  qsv=1;
  xw=i;
  c2=0;
  k=t;

  while (1) {
      if (!(o < t)) {
          break;
      }
      o = o + 1;
      if ((bjr == 0)) {
          k = k + i;
      }
      if ((bjr == 1)) {
          h = h + i;
      }
      if (!(!(((i % 2) != 0)))) {
          bjr = 0;
      }
      else {
          bjr = 1;
      }
      i = i + 1;
      c2 = c2 + k;
      qsv = qsv + k;
      xw += bjr;
      qsv++;
      xw = xw - 1;
  }

}
