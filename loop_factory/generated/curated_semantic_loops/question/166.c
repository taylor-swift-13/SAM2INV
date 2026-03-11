int main1(int b,int k){
  int n, u, e, v;

  n=b+11;
  u=1;
  e=0;
  v=n;


while (e<n) {
      if (e>=n/2) {
          v = v+2;
      }
      e = e+1;
  }
/*@
  assert !(e<n) &&
         (n == b + 11);
*/

}
