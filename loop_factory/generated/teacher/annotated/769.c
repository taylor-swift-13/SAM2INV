int main1(int b,int m,int n,int q){
  int u, i, z, j, v;

  u=m-7;
  i=0;
  z=b;
  j=i;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z >= b;
  loop invariant j == b*(z - b) + ((z - b) * (z - b + 1)) / 2;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j == b*(z - b) + (z - b)*(z - b + 1)/2;
  loop invariant j == \at(b,Pre) * (z - \at(b,Pre)) + ((z - \at(b,Pre)) * (z - \at(b,Pre) + 1)) / 2;
  loop invariant z >= \at(b,Pre);
  loop invariant u == \at(m,Pre) - 7;

  loop invariant u == m - 7;
  loop assigns z, j;
*/
while (1) {
      z = z+1;
      j = j+z;
  }

}
