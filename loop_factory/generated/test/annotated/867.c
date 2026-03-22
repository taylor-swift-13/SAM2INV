int main1(int k,int z){
  int vsx, dh6, j;
  vsx=k-2;
  dh6=0;
  j=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 1;
  loop invariant k == \at(k, Pre) + j*(j+1)/2 - 1;
  loop invariant (z == \at(z, Pre));
  loop invariant vsx <= \at(k, Pre) - 2;
  loop assigns j, k, vsx;
*/
while (dh6+1<=vsx) {
      j++;
      k += j;
      vsx = (dh6+1)-1;
  }
}