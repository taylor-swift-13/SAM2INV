int main1(int z,int f){
  int a, li4, c4q, oam, xp;
  a=(f%38)+16;
  li4=a;
  c4q=3;
  oam=0;
  xp=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oam == c4q * (li4 - a);
  loop invariant z == \at(z, Pre) + 2 * (li4 - a);
  loop invariant a == (\at(f,Pre) % 38) + 16;
  loop invariant oam == 3*(li4 - a);
  loop invariant li4 >= a;
  loop assigns oam, z, li4;
*/
while (1) {
      if (!(li4-4>=0)) {
          break;
      }
      oam += c4q;
      z += 2;
      li4++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z - \at(z, Pre) >= 0;
  loop assigns oam, z, xp;
*/
while (xp>4) {
      oam = oam+a*xp;
      z += xp;
      xp = 4;
  }
}