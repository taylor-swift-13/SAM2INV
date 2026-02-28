int main1(int m,int q){
  int n, f, z, v, x;

  n=77;
  f=0;
  z=q;
  v=n;
  x=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f >= 0 && f <= n && z == q + f && v == n - f && v + z == n + q;
  loop invariant z - f == q;
  loop invariant z == \at(q, Pre) + f && v == n - f;
  loop invariant 0 <= f && f <= n;
  loop invariant z == \at(q, Pre) + f && v == n - f && f <= n;
  loop invariant m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant f <= n;
  loop invariant f >= 0;
  loop invariant z == q + f;
  loop invariant v == n - f;
  loop invariant n == 77;
  loop assigns z, v, f;
*/
while (f<n) {
      z = z+1;
      v = v-1;
      f = f+1;
  }

}
