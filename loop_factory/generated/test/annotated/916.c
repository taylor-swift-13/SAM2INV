int main1(int f,int u){
  int t5, vd, h, ltp;
  t5=u*5;
  vd=t5;
  h=0;
  ltp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == ltp % 3;
  loop invariant f == \at(f, Pre) + ltp * (t5 + 4);
  loop invariant f == \at(f, Pre) + ltp * (vd + 4);
  loop invariant 0 <= ltp;
  loop invariant (t5 >= 0) ==> (ltp <= t5);
  loop assigns f, h, ltp;
*/
while (1) {
      if (!(ltp<t5)) {
          break;
      }
      h = (h+1)%3;
      ltp = ltp + 1;
      f += vd;
      f += 4;
  }
}