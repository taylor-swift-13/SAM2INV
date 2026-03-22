int main1(){
  int r90, dz, x4k, l;
  r90=1;
  dz=0;
  x4k=0;
  l=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x4k == dz;
  loop invariant l == dz * (dz + 1) / 2;
  loop invariant dz <= r90;
  loop assigns dz, x4k, l;
*/
while (dz < r90) {
      dz = dz + 1;
      x4k = x4k + 1;
      l = l + x4k;
  }
}