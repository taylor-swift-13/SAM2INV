int main1(int a,int p){
  int f, z, v, i;

  f=33;
  z=1;
  v=-6;
  i=f;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 33;
  loop invariant z <= f;
  loop invariant z >= 1;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant z > 0;
  loop invariant z >= 1 && (z == 1 || z % 3 == 0) && z <= f;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && f == 33;
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && (z == 1 || z % 3 == 0);
  loop invariant 1 <= z && z <= f && f - z >= 0;
  loop invariant (z == 1 || z == 3 || z == 9 || z == 27) && (a == \at(a, Pre)) && (p == \at(p, Pre));
  loop invariant z >= 1 && z <= f;
  loop assigns z;
*/
while (z*3<=f) {
      z = z*3;
  }

}
