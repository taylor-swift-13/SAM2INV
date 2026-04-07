int main1(){
  int d, xh, br, m, hg;
  d=1;
  xh=d;
  br=d;
  m=10;
  hg=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 6*hg + 4;
  loop invariant br == 3*hg*hg + hg - 3;
  loop invariant xh == hg*hg*hg - hg*hg - 3*hg + 4;
  loop invariant hg >= 1;
  loop invariant d == 1;
  loop assigns xh, br, m, hg;
*/
while (1) {
      if (hg>d) {
          break;
      }
      xh += br;
      br = br + m;
      m += 6;
      hg = hg + 1;
  }
}