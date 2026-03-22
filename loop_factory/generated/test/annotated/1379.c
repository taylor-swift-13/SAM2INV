int main1(){
  int z, k, wd, f3m, ye, oy;
  z=(1%35)+15;
  k=(1%35)+15;
  wd=1;
  f3m=0;
  ye=0;
  oy=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z > 0;
  loop invariant k > 0;
  loop invariant z + k <= 32;
  loop invariant z*oy - k*ye == 16;
  loop assigns z, k, wd, f3m, ye, oy;
*/
while (1) {
      if (!(z!=k)) {
          break;
      }
      if (z>k) {
          z = z - k;
          wd -= f3m;
          ye -= oy;
      }
      else {
          k -= z;
          f3m = f3m - wd;
          oy -= ye;
      }
      wd = wd*2;
  }
}