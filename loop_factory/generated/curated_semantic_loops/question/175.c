int main1(int a,int p){
  int n, b, s, v;

  n=(p%40)+5;
  b=0;
  s=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (s<n) {
      if (s<n/2) {
          v = v+3;
      }
      else {
          v = v-3;
      }
      s = s+1;
  }
/*@
  assert (n == (\at(p, Pre) % 40) + 5) &&
         (s >= n) &&
         (s >= 0) &&
         (v % 3 == 0);
*/

}
