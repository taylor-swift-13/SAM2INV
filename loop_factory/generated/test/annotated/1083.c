int main1(int o){
  int jp, z, j262, ys, a3, slcn;
  jp=157;
  z=0;
  j262=0;
  ys=(o%28)+10;
  a3=0;
  slcn=o+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j262 >= 0;
  loop invariant slcn == \at(o, Pre) + 2 + j262;
  loop invariant ys == ((\at(o, Pre) % 28) + 10) - j262*(j262 - 1)/2;
  loop invariant a3 == 0;
  loop invariant jp == 157;
  loop invariant o >= \at(o, Pre);
  loop invariant o <= \at(o, Pre) + 2 * j262;
  loop assigns ys, slcn, a3, o, j262;
*/
while (1) {
      if (!(ys>j262)) {
          break;
      }
      ys -= j262;
      slcn = (1)+(slcn);
      a3 = a3*4;
      o = o+(ys%3);
      j262 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j262 >= 0;
  loop invariant o >= \at(o, Pre);
  loop invariant jp == z + 157;
  loop assigns jp, z, slcn, j262, o;
*/
while (slcn>0) {
      jp = jp+o*o;
      z = z+o*o;
      slcn--;
      j262 = j262+o*o;
      o = o+(j262%9);
  }
}