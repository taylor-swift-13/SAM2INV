int main1(int s,int b){
  int y8v, kh, nbu, a9u, le;
  y8v=s;
  kh=0;
  nbu=0;
  a9u=0;
  le=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nbu == a9u * s;
  loop invariant 0 <= a9u;
  loop invariant y8v == s;
  loop assigns a9u, nbu;
*/
while (1) {
      if (!(a9u<=y8v-1)) {
          break;
      }
      a9u++;
      nbu = nbu + s;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a9u - s*kh >= 0;
  loop invariant kh >= 0;
  loop assigns a9u, kh;
*/
while (kh<le) {
      a9u = a9u + s;
      kh++;
  }
}