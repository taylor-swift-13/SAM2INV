int main1(){
  int s, cu, wl, ofd, d9;
  s=1*4;
  cu=0;
  wl=0;
  ofd=0;
  d9=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= wl <= s;
  loop invariant 0 < d9 <= 6;
  loop invariant ofd == wl*(6 + cu) - wl*(wl - 1)/2;
  loop invariant d9 + wl == 6;
  loop assigns wl, d9, ofd;
*/
while (wl<s&&d9>0) {
      wl += 1;
      ofd = ofd + d9;
      d9 -= 1;
      ofd += cu;
  }
}