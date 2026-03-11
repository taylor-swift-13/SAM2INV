int main1(int c,int f){
  int kzeq, y, nsx3, q1, x1;
  kzeq=f+11;
  y=4;
  nsx3=0;
  q1=3;
  x1=f;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kzeq == f + 11;
  loop invariant y == 4;
  loop invariant c == \at(c, Pre);
  loop invariant q1 == 3 + nsx3*(nsx3 - 1)/2;
  loop invariant x1 == f + 4*nsx3;
  loop invariant f == \at(f, Pre);
  loop invariant 0 <= nsx3;
  loop assigns q1, x1, nsx3;
*/
while (nsx3<=kzeq-1) {
      q1 += nsx3;
      x1 = x1 + y;
      nsx3 = nsx3 + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4 <= y;
  loop invariant c == \at(c, Pre) + (y - 4) * kzeq - 4 * (y - 4) - ((y - 4) * (y - 5)) / 2;
  loop invariant kzeq == \at(f, Pre) + 11;
  loop assigns q1, y, c;
*/
while (y<kzeq) {
      q1 = kzeq-y;
      y++;
      c += q1;
  }
/*@
  assert !(y<kzeq) &&
         (kzeq == f + 11);
*/

}