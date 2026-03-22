int main1(){
  int zu, m, c5o, le, dk, f, u1, nc8;
  zu=1+11;
  m=0;
  c5o=0;
  le=0;
  dk=0;
  f=0;
  u1=0;
  nc8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= m;
  loop invariant m <= zu;
  loop invariant c5o == m/2;
  loop invariant le == m;
  loop invariant dk == (m+1)/2;
  loop invariant f == m/3;
  loop invariant u1 == (m/3) % 5;
  loop invariant nc8 >= m;
  loop assigns m, c5o, le, dk, f, u1, nc8;
*/
while (1) {
      if (!(m < zu)) {
          break;
      }
      m++;
      if ((m % 2) == 0) {
          c5o += 1;
      }
      if ((m % 3) == 0) {
          f = f + 1;
          u1 = (u1 + 1) % 5;
      }
      else {
      }
      le += 1;
      dk = dk+(m%2);
      nc8 = nc8 + c5o;
      nc8++;
  }
}