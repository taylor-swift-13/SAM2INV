int main1(int y,int z){
  int fnb, n, sf, sh5j, tibt;
  fnb=z-7;
  n=0;
  sf=0;
  sh5j=-4;
  tibt=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == \at(y, Pre) + sf*(sf+1)/2;
  loop invariant 0 <= sf;
  loop invariant fnb == \at(z,Pre) - 7;
  loop invariant z == \at(z,Pre);
  loop invariant tibt == sf + 8;
  loop assigns sf, tibt, n, y;
*/
while (sf<fnb) {
      sf++;
      tibt = tibt + 1;
      n = n + y;
      y = y + sf;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tibt >= fnb + 6;
  loop invariant fnb == \at(z,Pre) - 7;
  loop assigns n, sh5j, z, tibt;
*/
while (fnb+7<=tibt) {
      n += sh5j;
      sh5j = sh5j+(n%4);
      z += n;
      tibt = (fnb+7)-1;
  }
}