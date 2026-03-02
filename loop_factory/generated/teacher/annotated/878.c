int main1(int b,int n){
  int o, j, z;

  o=22;
  j=0;
  z=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 22;
  loop invariant o == 22;
  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant z >= o;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);

  loop invariant z >= 22 && o == 22;
  loop invariant b == \at(b, Pre) && n == \at(n, Pre) && z > 0;
  loop assigns z;
*/
while (1) {
      z = z+3;
      z = z*z;
  }

}
