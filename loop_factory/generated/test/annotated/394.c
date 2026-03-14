int main1(){
  int e8, pb, nls, m, u93d;
  e8=(1%15)+15;
  pb=0;
  nls=0;
  m=0;
  u93d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pb == nls*5 + m;
  loop invariant 0 <= m;
  loop invariant m < 5;
  loop invariant 0 <= pb;
  loop invariant pb <= e8;
  loop invariant 0 <= nls;
  loop invariant nls <= e8/5;
  loop invariant u93d == 5 * nls + m;
  loop assigns u93d, m, nls, pb;
*/
while (1) {
      if (!(pb<=e8-1)) {
          break;
      }
      u93d++;
      m++;
      if (m>=5) {
          m = m - 5;
          nls = nls + 1;
      }
      pb = pb + 1;
  }
}