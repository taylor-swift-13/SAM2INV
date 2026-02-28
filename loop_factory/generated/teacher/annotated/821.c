int main1(int a,int n){
  int x, k, v, z;

  x=77;
  k=1;
  v=k;
  z=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == (2*k) - 1;
  loop invariant z == k*k + k + 75;
  loop invariant k <= x;
  loop invariant x == 77;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v == 2*k - 1);
  loop invariant (z == k*k + k + 75);
  loop invariant (1 <= k);
  loop invariant (k <= x);
  loop invariant v == 2*k - 1;
  loop invariant k >= 1;
  loop invariant z == x + (k*k) + k - 2;
  loop assigns v, k, z;
*/
while (1) {
      if (k>=x) {
          break;
      }
      v = v+1;
      k = k+1;
      v = v+1;
      z = z+v;
      z = z+1;
  }

}
