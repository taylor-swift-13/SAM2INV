int main1(){
  int rox, xv, xd, m;
  rox=1+23;
  xv=0;
  xd=0;
  m=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 0;
  loop invariant (xd == 0) || (xd == 1);
  loop invariant xv <= rox;
  loop invariant rox == 1 + 23;
  loop invariant 0 <= xd;
  loop invariant 0 <= xv;
  loop assigns m, xd, xv;
*/
for (; xd>0&&xv<rox; xv++) {
      if (xd<xd) {
          xd = xd;
      }
      else {
          xd = xd;
      }
      xd -= xd;
      m += xd;
      xd++;
  }
}