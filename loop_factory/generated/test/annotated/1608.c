int main1(){
  int e33b, h, ii, yh, tg, vv, f, om0x;
  e33b=33;
  h=e33b;
  ii=0;
  yh=0;
  tg=0;
  vv=(1%18)+5;
  f=-4;
  om0x=h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yh == ii;
  loop invariant 0 <= vv <= 6;
  loop invariant e33b == 33;
  loop invariant h == 33;
  loop invariant ii + vv == 6;
  loop invariant om0x == e33b + 6*ii - (ii*(ii+1))/2;
  loop invariant (tg == ii);
  loop assigns vv, tg, ii, yh, f, om0x;
*/
while (vv>0) {
      vv = vv - 1;
      tg = tg+1*1;
      ii = ii+1*1;
      yh = yh+1*1;
      if (h+4<=om0x+e33b) {
          f += om0x;
      }
      if (h+2<=e33b+e33b) {
          f = f%4;
      }
      om0x += vv;
      f = f*3+1;
  }
}