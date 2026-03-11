int main1(int a,int b){
  int u, d, n, e;

  u=b+12;
  d=u;
  n=0;
  e=a;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (n<u) {
      if (n>=u/2) {
          e = e+4;
      }
      n = n+1;
      n = n*3+3;
  }
/*@
  assert (u == \at(b, Pre) + 12) &&
         (n >= u) &&
         (n % 3 == 0) &&
         (e >= \at(a, Pre)) &&
         ((e - \at(a, Pre)) % 4 == 0);
*/

}
