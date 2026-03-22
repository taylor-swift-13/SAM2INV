int main1(){
  int bn0, vw, l, nhi, k6, po;
  bn0=1;
  vw=1;
  l=8;
  nhi=4;
  k6=bn0;
  po=bn0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bn0 == 1;
  loop invariant vw > 0;
  loop assigns vw;
*/
for (; vw<=bn0/3; vw = vw*3) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bn0 + po == 2;
  loop invariant nhi >= 4;
  loop invariant l == 2 * nhi;
  loop invariant l - nhi*(k6+1) == 0;
  loop invariant po >= 0;
  loop assigns po, bn0, l, nhi;
*/
while (po>=1) {
      po -= 1;
      bn0 = bn0+1*1;
      l = l+1*1;
      nhi = nhi+1*1;
      l = l + k6;
  }
}