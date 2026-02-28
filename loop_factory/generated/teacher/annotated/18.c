int main1(int b,int n){
  int t, j, l, z, q, s;

  t=38;
  j=0;
  l=t;
  z=n;
  q=n;
  s=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= j <= t && l == t + j;
  loop invariant z == n + j * t + j*(j+1)/2 && n == \at(n, Pre) && b == \at(b, Pre);
  loop invariant l == t + j;
  loop invariant z == \at(n,Pre) + t*j + j*(j+1)/2;
  loop invariant j <= t;
  loop invariant b == \at(b,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant l == j + 38;
  loop invariant z == n + 38*j + j*(j+1)/2;
  loop invariant l == 38 + j;
  loop invariant z == \at(n, Pre) + 38*j + j*(j+1)/2;
  loop invariant z == n + t*j + j*(j+1)/2;
  loop invariant j >= 0;
  loop assigns j, l, z;
*/
while (j<t) {
      l = l+1;
      z = z+l;
      j = j+1;
  }

}
