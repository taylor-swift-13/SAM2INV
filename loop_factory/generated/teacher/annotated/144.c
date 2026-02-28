int main1(int p){
  int z, k, s, o;

  z=p;
  k=z;
  s=z;
  o=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == p;
  loop invariant p == \at(p, Pre);
  loop invariant s <= z;
  loop invariant ((z - s) % 2) == 0;
  loop invariant 0 <= z - s;
  loop invariant s <= z + 1;
  loop invariant s >= p;
  loop invariant z == \at(p, Pre);
  loop invariant s >= \at(p, Pre);
  loop invariant (s - \at(p, Pre)) % 2 == 0;
  loop invariant ((s - z) % 2) == 0;
  loop assigns s;
*/
while (s<z) {
      if (s<z) {
          s = s+1;
      }
      s = s+1;
  }

}
