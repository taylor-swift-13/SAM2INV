int main1(){
  int gcc, d8, hg, hx, kx;
  gcc=1;
  d8=0;
  hg=d8;
  hx=-3;
  kx=gcc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hx == -3 + d8;
  loop invariant hg == -3*d8 + d8*(d8-1)/2;
  loop invariant 0 <= d8;
  loop invariant d8 <= gcc;
  loop invariant 2*hg == d8*(d8 - 7);
  loop invariant kx == 1 + ((d8 + 1) / 3);
  loop assigns hg, d8, hx, kx;
*/
while (d8 < gcc) {
      hg += hx;
      d8 = d8 + 1;
      hx += 1;
      kx = kx+(hg%3);
  }
}