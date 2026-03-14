int main1(int j){
  int kq, jm, h3mn, k, d2, ko;
  kq=(j%37)+18;
  jm=0;
  h3mn=0;
  k=0;
  d2=jm;
  ko=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d2 == k * kq;
  loop invariant h3mn == k * j;
  loop invariant k >= 0;
  loop assigns { d2, k, h3mn };
*/
while (k<=kq-1) {
      d2 += kq;
      k += 1;
      h3mn += j;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(j, Pre) + ko * (d2 - h3mn);
  loop invariant ko >= 0;
  loop assigns { ko, jm, j };
*/
while (ko<d2) {
      ko += 1;
      jm += j;
      j = j+d2-h3mn;
  }
}