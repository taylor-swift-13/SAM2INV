int main1(int b,int q){
  int h, v, z;

  h=40;
  v=0;
  z=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 40;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= z && z <= 4;
  loop invariant b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant 0 <= z && z <= 4 && h == 40 && b == \at(b, Pre);
  loop invariant 0 <= z && z < 5;
  loop invariant z == z % 5;
  loop invariant h == 40 && b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant 0 <= z && z <= 4 && z == (z + 5) % 5;
  loop invariant z >= 0 && z <= 4;
  loop invariant 0 <= z && z <= 4 && z == z % 5;
  loop assigns z;
*/
while (1) {
      z = z+3;
      z = z%5;
  }

}
