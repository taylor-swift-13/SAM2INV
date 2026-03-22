int main1(){
  int p, pvd, pi, yomn, r2g, qe, iw, gyfw, f6qx, gr, e;

  p=8;
  pvd=p;
  pi=7;
  yomn=7;
  r2g=0;
  qe=7;
  iw=0;
  gyfw=-3;
  f6qx=-8;
  gr=-1;
  e=4;

  while (pvd<p) {
      if (pvd%3==0) {
          if (pi>0) {
              pi -= 1;
              r2g = r2g + 1;
          }
      }
      else {
          if (pi<qe) {
              pi++;
              yomn++;
          }
      }
      pvd = pvd + 1;
      gyfw++;
      iw += 1;
      e = e + pi;
      gr = gr + 3;
      f6qx += iw;
      qe++;
  }

}
