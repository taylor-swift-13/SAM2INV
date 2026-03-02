int main1(int b,int m){
  int h, o, v, z;

  h=b;
  o=0;
  v=1;
  z=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 0;
  loop invariant h == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant v > 0;
  loop invariant h == b && o == 0;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre) && v > 0;
  loop invariant h == b;
  loop invariant v >= 1;
  loop invariant (v == 1) || (v % 2 == 0);

  loop invariant h == \at(b, Pre) && b == \at(b, Pre) && m == \at(m, Pre);
  loop invariant o == 0 && v >= 1;
  loop assigns v, o;
*/
while (1) {
      v = v*2;
      o = o;
  }

}
