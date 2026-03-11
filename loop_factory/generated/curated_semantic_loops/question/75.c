int main1(int b,int k){
  int d, m, p, s;

  d=k;
  m=2;
  p=k;
  s=b;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (p<d) {
      if (p<d) {
          p = p+1;
      }
      p = p+1;
  }
/*@
  assert !(p<d) &&
         (d == k);
*/

}
