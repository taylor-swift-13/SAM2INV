int main1(){
  int d7, emc3, mc, m4, cv6, p6mp, aw;
  d7=1;
  emc3=d7;
  mc=0;
  m4=0;
  cv6=1;
  p6mp=(1%35)+8;
  aw=emc3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p6mp;
  loop invariant p6mp <= 9;
  loop invariant aw >= 1;
  loop invariant m4 >= 0;
  loop invariant mc >= 0;
  loop invariant cv6 == m4 + 1;
  loop invariant d7 == 1;
  loop assigns aw, cv6, m4, mc, p6mp;
*/
while (p6mp>0) {
      mc = mc+m4*m4;
      cv6 = cv6+p6mp*p6mp;
      m4 = m4+p6mp*p6mp;
      p6mp--;
      aw += mc;
  }
}