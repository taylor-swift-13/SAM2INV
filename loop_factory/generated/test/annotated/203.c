int main1(int e,int z){
  int r2;
  r2=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r2 == -2 || r2 == 0;
  loop invariant z == \at(z, Pre);
  loop invariant e == \at(e, Pre) + 2 + r2;
  loop assigns r2, e, z;
*/
while (r2!=0&&r2!=0) {
      if (r2>r2) {
          r2 -= r2;
      }
      else {
          r2 -= r2;
      }
      e += 2;
      z += r2;
  }
}