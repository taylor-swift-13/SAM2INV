int main1(){
  int t05h, lnen, jmh, ozw, u, d;
  t05h=(1%18)+15;
  lnen=0;
  jmh=0;
  ozw=-2;
  u=-2;
  d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t05h == 16;
  loop invariant d == 0;
  loop invariant u == 2*ozw + 2;
  loop invariant jmh == ozw + 2;
  loop invariant lnen == 0;
  loop invariant ozw <= t05h;
  loop invariant 0 <= jmh;
  loop assigns ozw, jmh, u, d;
*/
while (ozw<t05h) {
      ozw++;
      jmh++;
      u += 2;
      d = d + lnen;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d <= jmh;
  loop assigns u, t05h, d;
*/
while (1) {
      u = u+t05h*d;
      t05h = t05h + u;
      t05h = t05h*3+1;
      d++;
      if (d>=jmh) {
          break;
      }
  }
}