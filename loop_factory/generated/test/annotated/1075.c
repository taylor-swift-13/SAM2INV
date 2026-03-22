int main1(int m){
  int y, f0t, ky, p, pvf, lwy, cc;
  y=20;
  f0t=2;
  ky=0;
  p=0;
  pvf=0;
  lwy=(m%18)+5;
  cc=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cc == 20 + f0t * (((\at(m, Pre) % 18) + 5) - lwy);
  loop invariant ky == p;
  loop invariant lwy <= ((\at(m, Pre) % 18) + 5);
  loop invariant ky == pvf;
  loop invariant m >= \at(m, Pre);
  loop invariant cc >= 20;
  loop invariant y == 20;
  loop invariant ky == ((\at(m,Pre) % 18) + 5 - lwy) * m * m;
  loop assigns pvf, cc, ky, p, lwy;
*/
while (lwy>0) {
      pvf = pvf+m*m;
      cc += f0t;
      ky = ky+m*m;
      p = p+m*m;
      lwy--;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m >= \at(m, Pre);
  loop invariant cc >= 20;
  loop invariant ky >= 0;
  loop assigns ky, lwy, y, m, cc;
*/
while (1) {
      if (!(ky>lwy)) {
          break;
      }
      ky -= lwy;
      lwy = lwy + 1;
      y = y+(lwy%2);
      m += ky;
      cc = cc+(ky%3);
  }
}