int main1(){
  int t, b6s, om, u4, pc;
  t=1;
  b6s=2;
  om=0;
  u4=b6s;
  pc=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (pc == 1);
  loop invariant (om * om) == (4 * (u4 - 2));
  loop invariant pc <= om + 1;
  loop invariant t == 1;
  loop invariant om <= t + 1;
  loop assigns om, pc, u4;
*/
while (om<=t-1) {
      om += 2;
      if (om<=pc) {
          pc = om;
      }
      u4 = u4+om-pc;
  }
}