int main1(int b,int k){
  int m, j, v, z;

  m=b;
  j=1;
  v=0;
  z=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant (v > 0) ==> (z + v == m + 1);
  loop invariant m == b;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (v > 0) ==> z == m - (v - 1);
  loop invariant m == \at(b, Pre);
  loop invariant z <= m;
  loop invariant (v == 0) ==> (z == m);
  loop invariant (v > 0) ==> (z == m - v + 1);
  loop invariant (v == 0) ==> (z + v == m);
  loop invariant (v >= 1) ==> (z + v == m + 1);
  loop assigns z, v;
*/
while (1) {
      z = m-v;
      v = v+1;
  }

}
