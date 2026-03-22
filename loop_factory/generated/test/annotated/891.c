int main1(int p){
  int lu, nl4, pc, unr, m26a;
  lu=p-6;
  nl4=0;
  pc=0;
  unr=0;
  m26a=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m26a == 5 - pc;
  loop invariant p == \at(p, Pre) + nl4 * pc &&
                 unr == 5 * pc - pc * (pc - 1) / 2;
  loop invariant unr == pc*(11 - pc)/2;
  loop invariant p == \at(p, Pre) + pc * nl4;
  loop invariant 0 <= pc;
  loop invariant 0 <= m26a;
  loop assigns pc, unr, p, m26a;
*/
while (pc<lu&&m26a>0) {
      pc++;
      unr += m26a;
      p += nl4;
      m26a -= 1;
  }
}