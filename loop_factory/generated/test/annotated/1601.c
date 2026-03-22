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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= pi <= qe;
  loop invariant pvd <= p;
  loop invariant gr >= -1;
  loop invariant e >= 4;
  loop invariant yomn >= 7;
  loop invariant p == 8;
  loop invariant pvd == qe + 1;
  loop invariant gr == -1 + 3*(qe - 7);
  loop invariant gyfw == qe - 10;
  loop invariant iw == qe - 7;
  loop invariant f6qx == -8 + iw*(iw+1)/2;
  loop invariant yomn <= qe;
  loop invariant r2g >= 0;
  loop assigns pi, r2g, pvd, gyfw, iw, e, gr, f6qx, qe, yomn;
*/
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