int main1(int p,int q){
  int x, z, s;

  x=40;
  z=1;
  s=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 1;
  loop invariant z <= x;
  loop invariant z == 1 || z % 3 == 0;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x == 40;
  loop invariant (z == 1) || (z % 3 == 0);
  loop invariant z > 0;
  loop invariant z >= 1 && (z == 1 || z % 3 == 0) && z <= 3*(x/3);
  loop assigns z;
*/
while (z<=x/3) {
      z = z*3;
  }

}
