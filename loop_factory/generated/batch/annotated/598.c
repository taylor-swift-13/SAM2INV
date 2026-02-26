int main1(int b,int n){
  int o, j, z;

  o=22;
  j=0;
  z=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant o == 22;
  loop invariant j == 0;
  loop invariant z >= o;
  loop invariant z >= 0;
  loop invariant z >= 22;
  loop assigns z;
*/
while (1) {
      z = z+3;
      z = z*z;
      if ((j%2)==0) {
          z = z*z;
      }
  }

}
