int main1(int h,int b){
  int qk, ebc, vgz, y, qp;
  qk=h+14;
  ebc=0;
  vgz=0;
  y=(h%28)+10;
  qp=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(h,Pre) + vgz;
  loop invariant qp == 6 + 3 * vgz;
  loop invariant ebc == 0;
  loop invariant b == \at(b,Pre) + vgz * ( \at(h,Pre) + 14 );
  loop invariant y == (\at(h,Pre) % 28) + 10 - vgz*(vgz - 1)/2;
  loop invariant qk == \at(h,Pre) + 14;
  loop assigns y, vgz, qp, b, h;
*/
while (y>vgz) {
      y = y - vgz;
      vgz++;
      qp = qp + 3;
      b = b+qk-ebc;
      h += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y + (vgz * (vgz - 1)) / 2 == (\at(h,Pre) % 28) + 10;
  loop invariant qk == \at(h,Pre) + 14;
  loop assigns y, vgz, h, b;
*/
while (y>vgz) {
      y = y - vgz;
      vgz++;
      h = h+(y%6);
      b = b+(y%7);
  }
}