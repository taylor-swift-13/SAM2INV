int main1(int b,int n){
  int z, y, k, f;

  z=n+8;
  y=0;
  k=5;
  f=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k >= 0;
  loop invariant f >= 0;
  loop invariant k + f <= 5;
  loop invariant k > 0;

  loop invariant z == \at(n,Pre) + 8;
  loop invariant b == \at(b,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant k <= 5;
  loop invariant f == 0;
  loop invariant z == n + 8;
  loop invariant f <= 5;
  loop invariant k % 5 == 0;
  loop invariant f % 5 == 0;
  loop assigns k, f;
*/
while (k!=0&&f!=0) {
      if (k>f) {
          k = k-f;
      }
      else {
          f = f-k;
      }
  }

}
