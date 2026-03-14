int main1(){
  int ca, o, wj, a5, bx3;
  ca=1;
  o=0;
  wj=0;
  a5=0;
  bx3=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a5 == wj;
  loop invariant bx3 == 6 - wj;
  loop invariant ca == 1;
  loop invariant o == a5 + wj;
  loop invariant 0 <= wj <= 6;
  loop assigns wj, a5, o, bx3;
*/
while (bx3>0) {
      wj = wj+1*1;
      a5 = a5+1*1;
      o = o+1*1;
      bx3 = (bx3)+(-(1));
      o += ca;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ca == 1;
  loop invariant wj >= 0;
  loop invariant wj <= 6;
  loop assigns wj;
*/
for (; wj>=1; wj = wj/2) {
  }
}