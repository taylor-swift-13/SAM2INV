int main1(int h){
  int e1ew, z;
  e1ew=19;
  z=e1ew;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e1ew == 19;
  loop invariant 0 <= z;
  loop invariant h >= \at(h, Pre);
  loop invariant z == e1ew;
  loop assigns h, z;
*/
while (z<e1ew&&z>0) {
      z += 1;
      z = z - 1;
      h += z;
  }
}