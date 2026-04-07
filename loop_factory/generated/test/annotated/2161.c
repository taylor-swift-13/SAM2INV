int main1(int p){
  int mq, x, wm, rx;
  mq=p+25;
  x=0;
  wm=p;
  rx=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mq == \at(p, Pre) + 25;
  loop invariant p == (\at(p, Pre) + (x*(x + 1))/2);
  loop invariant rx == wm;
  loop invariant 0 <= x;
  loop invariant (mq >= 0) ==> x <= mq;
  loop invariant p >= \at(p, Pre);
  loop invariant wm <= mq;
  loop assigns rx, x, wm, p;
*/
while (x < mq) {
      rx = rx + p < mq ? rx + p : mq;
      x = x + 1;
      wm = wm + p < mq ? wm + p : mq;
      p += x;
  }
}