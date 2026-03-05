int main1(int d){
  int sh6r, eam, g1j;
  sh6r=d+16;
  eam=sh6r;
  g1j=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sh6r == \at(d, Pre) + 16;
  loop invariant sh6r - eam >= 0;
  loop invariant (g1j == 1) || (g1j == 2);
  loop assigns d, eam, g1j;
*/
while (eam<sh6r) {
      if (g1j>=10) {
          g1j = -1;
      }
      if (g1j<=3) {
          g1j = 1;
      }
      g1j += g1j;
      eam++;
      d = d + eam;
  }
}