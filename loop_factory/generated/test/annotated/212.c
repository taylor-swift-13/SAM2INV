int main1(int o){
  int hb, t, ced, rb;
  hb=19;
  t=0;
  ced=0;
  rb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rb == (ced*(ced+1))/2;
  loop invariant t == 0;
  loop invariant hb >= t;
  loop invariant ced >= 0;
  loop assigns ced, rb, hb;
*/
while (t+1<=hb) {
      ced = ced + 1;
      rb += ced;
      hb = (t+1)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant rb >= 0;
  loop invariant o >= \at(o, Pre);
  loop invariant ced >= 0;
  loop invariant o == \at(o, Pre) + ced*(rb - ced*(ced+1)/2);
  loop invariant hb <= t;
  loop assigns hb, o, rb;
*/
while (rb<=t-1) {
      hb = t-rb;
      o += ced;
      rb += 1;
  }
}