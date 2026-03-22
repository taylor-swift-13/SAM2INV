int main1(){
  int db, m7o, w, gg, o, ta;
  db=1*2;
  m7o=db+1;
  w=(1%40)+2;
  gg=0;
  o=2;
  ta=m7o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m7o == db + 1;
  loop invariant w == 1 || w == 3;
  loop invariant gg == 0 || gg == 1 || gg == 3;
  loop invariant o >= 2;
  loop invariant ta >= 3;
  loop invariant db == 2;
  loop assigns gg, w, o, ta;
*/
while (1) {
      if (!(w!=gg)) {
          break;
      }
      gg = w;
      w = (w+db/w)/2;
      o = o + w;
      ta = ta+(w%2);
      o = o + m7o;
      ta = ta*ta;
  }
}