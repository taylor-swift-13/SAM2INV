int main1(int q){
  int w, z, r;

  w=40;
  z=1;
  r=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*r + 5*z == 13;
  loop invariant q == \at(q, Pre);
  loop invariant w == 40;
  loop invariant z >= 1;
  loop invariant r <= 2;
  loop invariant (z - 1) % 4 == 0;
  loop invariant r == 2 - 5 * ((z - 1) / 4);
  loop invariant 1 <= z;
  loop invariant z <= w;
  loop invariant z % 4 == 1;
  loop invariant 5*(z-1) + 4*(r-2) == 0;
  loop assigns r, z;
*/
while (z<=w-4) {
      r = r-6;
      r = r+1;
      z = z+4;
  }

}
