int main1(int b,int m){
  int h, o, v, z;

  h=b;
  o=0;
  v=1;
  z=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= 4;
  loop invariant o == 0;
  loop invariant v == 1;
  loop invariant h == b;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant z % 5 == 4;
  loop assigns z, o;
*/
while (1) {
      z = z+z;
      z = z+v;
      o = o;
  }

}
