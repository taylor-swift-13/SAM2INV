int main1(int z){
  int he, lvz, i, vt9, r1sj, k6r;
  he=18;
  lvz=1;
  i=3;
  vt9=0;
  r1sj=6;
  k6r=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r1sj == 6 + 3*vt9;
  loop invariant 0 <= vt9 <= he;
  loop invariant z == \at(z, Pre) + vt9 * (he - lvz);
  loop invariant he == 18;
  loop invariant lvz == 1;
  loop invariant i == 3 + vt9 * z - ((he - lvz) * (vt9 * (vt9 + 1) / 2));
  loop assigns i, r1sj, vt9, z;
*/
while (vt9<=he-1) {
      i += z;
      r1sj = r1sj + 3;
      vt9 = vt9 + 1;
      z = z+he-lvz;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= lvz <= k6r;
  loop invariant vt9 >= 0;
  loop invariant 1 <= lvz;
  loop invariant he == 18 + (lvz - 1) * z;
  loop assigns lvz, he, i, vt9;
*/
while (lvz<k6r) {
      lvz = lvz + 1;
      he += z;
      i = i + he;
      vt9 = vt9*vt9+vt9;
  }
}