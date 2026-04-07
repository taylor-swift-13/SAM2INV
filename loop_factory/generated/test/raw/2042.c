int main1(){
  int r, f92, kyww, xy, i, wx;

  r=1;
  f92=0;
  kyww=r;
  xy=r;
  i=2;
  wx=f92;

  while (1) {
      if (!(f92 < r)) {
          break;
      }
      f92 += 1;
      i = kyww - xy;
      kyww = kyww + (xy - kyww)/r;
      wx = wx + i/r;
  }

}
