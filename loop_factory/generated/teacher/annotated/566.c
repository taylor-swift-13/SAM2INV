int main1(int b,int n){
  int z, y, k, f;

  z=n+8;
  y=0;
  k=1;
  f=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0;
  loop invariant z == \at(n, Pre) + 8;
  loop invariant k >= 1;
  loop invariant (k - 1) % 4 == 0;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant ((k - 1) % 4) == 0;
  loop invariant z == n + 8;
  loop invariant k % 4 == 1;
  loop assigns k;
*/
while (1) {
      k = k+4;
      k = k+f;
  }

}
