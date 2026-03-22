int main1(){
  int ar, yr, qn, w, fu, gg, l;
  ar=1+4;
  yr=ar;
  qn=0;
  w=0;
  fu=0;
  gg=(1%18)+5;
  l=yr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fu == qn;
  loop invariant w == qn;
  loop invariant l == 5 + qn*(qn+1)/2;
  loop invariant gg >= 0;
  loop invariant ar == 5;
  loop invariant gg == 6 - qn;
  loop assigns qn, fu, w, gg, l;
*/
while (gg>0) {
      qn = qn+1*1;
      fu = fu+1*1;
      w = w+1*1;
      gg = gg - 1;
      l = l + w;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fu >= 0;
  loop invariant ar == 5;
  loop invariant gg == 0;
  loop invariant w == qn;
  loop invariant yr == 35 - 5*qn;
  loop invariant l == 2*qn + 14;
  loop assigns fu, yr, qn, l, w;
*/
while (fu>qn) {
      fu = fu - qn;
      yr = yr+gg-ar;
      qn++;
      l = (2)+(l);
      w += 1;
  }
}