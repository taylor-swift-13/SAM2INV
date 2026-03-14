int main1(int r,int b){
  int ue, tq, j, qp, c, el;
  ue=(r%30)+16;
  tq=ue+3;
  j=0;
  qp=(r%28)+10;
  c=b;
  el=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(r,Pre) + 2 * j;
  loop invariant tq == ue + 3;
  loop invariant ue == (\at(r,Pre) % 30) + 16;
  loop invariant qp == ((\at(r,Pre) % 28) + 10) - j*(j-1)/2;
  loop invariant el == tq * j;
  loop invariant 0 <= j;
  loop assigns qp, j, r, el, c;
*/
while (qp>j) {
      qp -= j;
      j++;
      r += 2;
      el = el + tq;
      c = c+(j%9);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 0;
  loop invariant tq == ((\at(r,Pre) % 30) + 19);
  loop invariant ue == (\at(r,Pre) % 30) + 16;
  loop assigns j;
*/
while (1) {
      j++;
      if (j>=tq) {
          break;
      }
  }
}