int main1(int g){
  int zdy, jg, r6v, hk;
  zdy=g+22;
  jg=zdy;
  r6v=0;
  hk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hk == r6v;
  loop invariant zdy == g + 22;
  loop invariant (jg == 0) || (jg == zdy);
  loop invariant g == \at(g,Pre);
  loop assigns hk, r6v, jg;
*/
while (jg > 0) {
      hk = hk + g;
      r6v = r6v + g;
      jg = 0;
  }
}