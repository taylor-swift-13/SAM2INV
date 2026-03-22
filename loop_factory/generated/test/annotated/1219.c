int main1(int b,int o){
  int a, a0y, bf, vr, e8, ei2, zx;
  a=b-7;
  a0y=0;
  bf=0;
  vr=1;
  e8=6;
  ei2=0;
  zx=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == b - 7;
  loop invariant a0y == 0;
  loop invariant ei2 >= 0;
  loop invariant e8 == 6 + 6 * ei2;
  loop invariant vr == 1 + 3 * ei2 * (ei2 + 1);
  loop invariant bf == ei2 * ei2 * ei2;
  loop invariant zx == b;
  loop invariant a == \at(b, Pre) - 7;
  loop invariant o == \at(o, Pre) + ei2*(ei2 + 1)/2;
  loop invariant zx == \at(b, Pre);
  loop assigns bf, ei2, vr, e8, o, zx;
*/
while (ei2<=a) {
      bf += vr;
      ei2++;
      vr = vr + e8;
      e8 += 6;
      o += ei2;
      zx += a0y;
  }
}