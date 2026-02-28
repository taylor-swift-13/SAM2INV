int main1(int k,int m){
  int z, j, g, q;

  z=m+8;
  j=0;
  g=5;
  q=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 5 + 2*j;
  loop invariant q == j*j + 6*j - 3;
  loop invariant z == m + 8;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant j >= 0;

  loop invariant q == -3 + j*(j+6);
  loop invariant z == \at(m, Pre) + 8;
  loop assigns g, j, q;
*/
while (1) {
      if (j>=z) {
          break;
      }
      g = g+1;
      j = j+1;
      g = g+1;
      q = q+g;
  }

}
