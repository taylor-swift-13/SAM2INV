int main1(int b,int m){
  int h, o, v, z;

  h=b;
  o=0;
  v=1;
  z=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 4;
  loop invariant z % 4 == 0;
  loop invariant o == 0;
  loop invariant h == \at(b, Pre) && b == \at(b, Pre) && m == \at(m, Pre);
  loop invariant h == \at(b, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant z >= 4 && z % 4 == 0;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre);
  loop invariant h == b;
  loop invariant z % 4 == 0 && z >= 4;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre) && h == \at(b, Pre);
  loop invariant z % 4 == 0 && z >= 4 && o == 0;
  loop assigns z, o;
*/
while (1) {
      z = z+z;
      o = o;
  }

}
