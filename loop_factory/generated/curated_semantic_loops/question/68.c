int main1(int b,int m){
  int k, j, p, d, w;

  k=14;
  j=k;
  p=-8;
  d=b;
  w=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (p<k) {
      if (p<k) {
          p = p+1;
      }
      p = p+1;
      d = d+p;
  }
/*@
  assert !(p<k) &&
         (4*d == 4*b + (p + 8) * (p - 6));
*/

}
