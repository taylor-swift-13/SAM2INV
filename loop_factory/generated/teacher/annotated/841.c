int main1(int a,int k,int n){
  int b, o, v, m, z;

  b=n+15;
  o=0;
  v=-1;
  m=6;
  z=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(n, Pre) + 15;
  loop invariant z == \at(n, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant v >= -1;
  loop invariant m <= 6;
  loop invariant z == n;
  loop invariant b == n + 15;
  loop invariant (m == 6) || (m == z);
  loop invariant z <= b;
  loop invariant (z <= m) ==> (m == z) && (z > m) ==> (m == 6) && n == \at(n, Pre) && a == \at(a, Pre) && k == \at(k, Pre);

  loop invariant n == \at(n, Pre);
  loop invariant a == \at(a, Pre) &&
                   k == \at(k, Pre) &&
                   n == \at(n, Pre) &&
                   z == n;

  loop assigns m, v;
*/
while (1) {
      if (v>=b) {
          break;
      }
      if (z<=m) {
          m = z;
      }
      v = v+1;
  }

}
