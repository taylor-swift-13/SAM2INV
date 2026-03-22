int main1(int q,int n){
  int vd, xh, yv, uq, mb;
  vd=38;
  xh=0;
  yv=1;
  uq=0;
  mb=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uq == (yv - 1) * yv * (2*yv - 1) / 6;
  loop invariant n == \at(n,Pre);
  loop invariant mb == \at(n,Pre) + 3*(yv - 1);
  loop invariant 1 <= yv <= vd + 1;
  loop assigns uq, n, yv, mb;
*/
while (yv<=vd) {
      uq = uq+yv*yv;
      n += xh;
      yv += 1;
      mb = mb + 3;
  }
}