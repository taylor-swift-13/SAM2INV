int main1(int k,int q){
  int n, z, b, v;

  n=k;
  z=0;
  b=-2;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - b + z == k + 2;
  loop invariant z >= 0;
  loop invariant n == k;
  loop invariant v >= k;
  loop invariant b >= -2;
  loop invariant b == (z*z + 3*z - 4)/2;
  loop invariant v == \at(k,Pre) + z*(z+1)/2;
  loop invariant n == \at(k,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant v - b + z == \at(k, Pre) + 2;
  loop invariant b == v + z - k - 2;
  loop invariant v == k + z*(z+1)/2;
  loop invariant b == -2 + z*(z+3)/2;
  loop assigns b, v, z;
*/
while (1) {
      b = b+2;
      v = v+1;
      b = b+z;
      v = v+z;
      z = z+1;
  }

}
