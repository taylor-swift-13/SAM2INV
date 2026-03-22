int main1(int p){
  int p90, w, ky55, l1sw, lzy, x, e, fg, m;

  p90=p;
  w=0;
  ky55=w;
  l1sw=0;
  lzy=p90;
  x=w;
  e=1;
  fg=p90;
  m=w;

  while (1) {
      if (!(w<=p90-1)) {
          break;
      }
      if (w%5==3) {
          ky55++;
      }
      else {
          l1sw++;
      }
      if (w%5==4) {
          lzy = lzy + 1;
      }
      else {
      }
      m = (m+ky55)%3;
      p += 2;
      fg = (fg+ky55)%3;
      x = (x+lzy)%8;
      m = x+e+fg;
      w = p90;
  }

}
