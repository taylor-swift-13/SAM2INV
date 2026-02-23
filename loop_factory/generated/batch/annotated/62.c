int main1(int a,int m){
  int w, k, z;

  w=17;
  k=0;
  z=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant (k == 0 ==> z == w) && (k > 0 ==> z == 0) && a == \at(a, Pre) && m == \at(m, Pre) && w == 17;
  loop invariant (k % 5 == 0) && (a == \at(a, Pre)) && (m == \at(m, Pre));
  loop invariant (k == 0) ==> (z == w);
  loop invariant (k != 0) ==> (z == 0);
  loop invariant k % 5 == 0;
  loop invariant 0 <= k;
  loop invariant k <= w + 4;
  loop invariant z == 0 || (k == 0 && z == w);
  loop invariant a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant w == 17;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant z == 0 || z == w;
  loop assigns z, k;
*/
while (k<w) {
      z = z+z;
      z = z-z;
      k = k+5;
  }

}
