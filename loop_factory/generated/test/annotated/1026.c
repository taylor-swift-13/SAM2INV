int main1(){
  int j1x, p, m, tmdw;
  j1x=1+4;
  p=0;
  m=0;
  tmdw=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= m;
  loop invariant m <= j1x;
  loop invariant tmdw >= p;
  loop invariant tmdw <= j1x;
  loop invariant tmdw + m <= j1x + 1;
  loop invariant 0 <= tmdw;
  loop invariant (m == 0) ==> (tmdw == 0);
  loop invariant (m > 0) ==> (tmdw + m == j1x + p + 1);
  loop assigns tmdw, m;
*/
while (m<j1x) {
      tmdw = j1x-m;
      tmdw += p;
      m++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tmdw < m;
  loop invariant 0 <= tmdw;
  loop invariant m == j1x;
  loop assigns tmdw;
*/
while (1) {
      tmdw = tmdw + 1;
      if (tmdw>=m) {
          break;
      }
  }
}