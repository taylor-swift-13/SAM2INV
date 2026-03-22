int main1(int r){
  int g9, ic, j, z, u;
  g9=r+14;
  ic=0;
  j=0;
  z=r+4;
  u=g9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 0;
  loop invariant ic == j * r;
  loop invariant z == r + 4 + j*(j + 1)/2;
  loop invariant g9 == r + 14;
  loop assigns j, ic, z;
*/
while (1) {
      if (!(j<=g9-1)) {
          break;
      }
      j++;
      ic += r;
      z += j;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 0;
  loop invariant u == g9;
  loop invariant g9 == r + 14;
  loop assigns j, ic;
*/
while (u*2<=ic) {
      j = j+g9*u;
      ic = (u*2)-1;
  }
}