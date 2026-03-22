int main1(){
  int a, y, omd0, sn, sin, h, vw;
  a=1;
  y=0;
  omd0=a;
  sn=12;
  sin=a;
  h=(1%6)+2;
  vw=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*vw + 36 == 3*sn;
  loop invariant h == 3;
  loop invariant sin >= 1;
  loop invariant vw >= 0;
  loop invariant omd0 >= 1;
  loop invariant sn == 12 + (h - 1) * vw;
  loop invariant sn >= 12;
  loop invariant a == 1;
  loop assigns omd0, sn, sin, vw;
*/
while (1) {
      if (sin>=a) {
          break;
      }
      omd0 = omd0*h+1;
      sn = sn*h;
      sin = sin + 1;
      vw = vw + sn;
  }
}