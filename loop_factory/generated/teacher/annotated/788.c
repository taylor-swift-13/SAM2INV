int main1(int k,int m){
  int z, j, v, n;

  z=k+16;
  j=0;
  v=m;
  n=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == m + 2*j;
  loop invariant n == 2 - j;
  loop invariant z == k + 16;

  loop invariant j >= 0;
  loop invariant z == \at(k,Pre) + 16;
  loop invariant n + j == 2;
  loop invariant v - 2*j == m;
  loop invariant m == \at(m,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant 0 <= j;
  loop assigns v, j, n;
*/
while (1) {
      if (j>=z) {
          break;
      }
      v = v+1;
      j = j+1;
      v = v+1;
      n = n-1;
  }

}
