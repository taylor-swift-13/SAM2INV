int main1(int o){
  int sp9p, lt, xm, p;
  sp9p=(o%28)+11;
  lt=0;
  xm=3;
  p=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sp9p + lt == (\at(o,Pre) % 28) + 11;
  loop invariant xm == p * lt + 3;
  loop invariant 0 <= lt;
  loop invariant sp9p == ((o % 28) + 11) - lt;
  loop assigns sp9p, lt, xm;
*/
while (lt < sp9p) {
      xm += p;
      lt += 1;
      sp9p = (sp9p)+(-(1));
  }
}