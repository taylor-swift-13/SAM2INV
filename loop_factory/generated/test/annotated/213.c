int main1(int z){
  int f, oo, rt;
  f=z;
  oo=f;
  rt=f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oo == \at(z, Pre);
  loop invariant z >= \at(z, Pre);
  loop invariant rt >= z;
  loop invariant oo == f;
  loop invariant rt >= f;
  loop invariant (\at(z, Pre) == 0 ==> z == \at(z, Pre)) && (\at(z, Pre) != 0 ==> (z - \at(z, Pre)) % \at(z, Pre) == 0);
  loop assigns rt, z;
*/
while (oo-2>=0) {
      rt += rt;
      z += oo;
  }
}