int main1(int b){
  int xm1, kxr, ce, gwy;
  xm1=(b%38)+17;
  kxr=0;
  ce=10;
  gwy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kxr % 4 == 0;
  loop invariant 8*gwy == -kxr*kxr + 2*(xm1+2)*kxr;
  loop invariant kxr >= 0;
  loop invariant (gwy >= 0);
  loop assigns ce, kxr, gwy;
*/
while (kxr<=xm1-1) {
      ce = (xm1)+(-(kxr));
      kxr += 4;
      gwy += ce;
  }
}