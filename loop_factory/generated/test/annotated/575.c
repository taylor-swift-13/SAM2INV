int main1(int i,int n){
  int b9lr, nz, nx3;
  b9lr=78;
  nz=0;
  nx3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nx3;
  loop invariant nx3 <= b9lr;
  loop invariant 0 <= nz;
  loop invariant nz == nx3 % 3;
  loop invariant n == \at(n,Pre) + 2*nx3;
  loop assigns nz, nx3, n, i;
*/
while (1) {
      if (!(nx3<b9lr)) {
          break;
      }
      nz = (nz+1)%3;
      nx3 += 1;
      n += 2;
      i = (i+nz)%8;
  }
}