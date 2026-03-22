int main1(){
  int wc, ij6, n, gn, w, xw, ppi, p8, phc;
  wc=1+8;
  ij6=0;
  n=-5;
  gn=0;
  w=0;
  xw=wc;
  ppi=20;
  p8=wc;
  phc=ij6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ij6 <= wc;
  loop invariant (ij6 < wc/2) ==> (gn == ij6);
  loop invariant (ij6 >= wc/2) ==> (gn == wc/2);
  loop invariant -5 <= n <= -1;
  loop invariant (ij6 < wc/2) ==> (n == -5 + ij6);
  loop invariant (ij6 >= wc/2) ==> (n == -5 + wc/2);
  loop invariant ppi >= 20;
  loop invariant p8 >= wc;
  loop invariant phc >= 0;
  loop invariant (ij6 <= wc/2) ==> (w == 0) && (xw == wc);
  loop invariant (ij6 > wc/2)  ==> (w == ij6 - wc/2) && (xw == wc + (ij6 - wc/2));
  loop assigns n, gn, w, xw, phc, ij6, ppi, p8;
*/
while (ij6 < wc) {
      if (ij6 < wc/2) {
          n += 1;
          gn = gn + 1;
      }
      if (ij6 >= wc/2) {
          w += 1;
          xw += 1;
      }
      else {
      }
      phc = phc + w;
      ij6++;
      ppi = ppi + 3;
      p8 = p8 + ppi;
      ppi += p8;
      phc += p8;
  }
}