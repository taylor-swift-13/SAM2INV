int main1(int a,int q){
  int g, z, v, x;

  g=64;
  z=g;
  v=z;
  x=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 1;
  loop invariant z <= 64;

  loop invariant g == 64;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 64 % z == 0;
  loop invariant 1 <= z;
  loop invariant z <= g;
  loop invariant g % z == 0;
  loop invariant z > 0;
  loop assigns z;
*/
while (z>1) {
      z = z/2;
  }

}
