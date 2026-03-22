int main1(int h,int a){
  int zfya, jx, x8, oe;
  zfya=(a%11)+10;
  jx=zfya;
  x8=0;
  oe=zfya;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x8 <= zfya;
  loop invariant oe == zfya - x8;
  loop invariant h == \at(h,Pre) + x8*(jx + 2);
  loop invariant jx == zfya;
  loop assigns oe, x8, h;
*/
while (x8<zfya&&oe>0) {
      oe = oe - 1;
      x8 += 1;
      h = (jx)+(h);
      h += 2;
  }
}