int main1(){
  int qcb, t, oo, wg;
  qcb=(1%28)+8;
  t=(1%22)+5;
  oo=0;
  wg=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= 0;
  loop invariant t <= 6;
  loop invariant oo >= 0;
  loop invariant oo % 9 == 0;
  loop invariant qcb > 0;
  loop invariant qcb % 9 == 0;
  loop invariant wg >= 4;
  loop assigns oo, qcb, wg, t;
*/
while (t!=0) {
      if (t%2==1) {
          oo += qcb;
          t = t - 1;
      }
      qcb = 2*qcb;
      wg = wg*2+(oo%3)+3;
      t = t/2;
  }
}