int main1(int p,int z){
  int g7, hlo, xb0d;
  g7=39;
  hlo=0;
  xb0d=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p,Pre) - hlo;
  loop invariant 0 <= hlo <= g7;
  loop invariant xb0d == 2 + hlo;
  loop invariant z == \at(z,Pre) + (hlo*(hlo - 1))/2;
  loop invariant xb0d == hlo + 2;
  loop invariant 0 <= hlo;
  loop invariant hlo <= g7;
  loop invariant 2*(z - \at(z, Pre)) == (hlo*(hlo - 1));
  loop assigns p, z, xb0d, hlo;
*/
while (1) {
      if (!(hlo+1<=g7)) {
          break;
      }
      z = z + hlo;
      xb0d = xb0d + 1;
      p -= 1;
      hlo += 1;
  }
}