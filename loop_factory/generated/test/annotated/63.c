int main1(){
  int mc, z0r, g, yl;
  mc=(1%30)+17;
  z0r=2;
  g=mc;
  yl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g - z0r == 16;
  loop invariant z0r <= mc;
  loop invariant yl <= 0;
  loop invariant g == mc + z0r - 2;
  loop invariant z0r >= 2;
  loop assigns g, z0r, yl;
*/
while (1) {
      yl -= 1;
      g++;
      yl = yl + yl;
      z0r += 1;
      if (z0r>=mc) {
          break;
      }
  }
}