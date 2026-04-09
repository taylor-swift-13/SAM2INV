int main1(int m){
  int w6d, m9ec, gvs, g7;
  w6d=28;
  m9ec=0;
  gvs=1;
  g7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= m9ec;
  loop invariant m9ec <= w6d;
  loop invariant (m == 1) ==> (g7 == m9ec);
  loop invariant (m - 1) * g7 + 1 == gvs;
  loop assigns g7, m9ec, gvs;
*/
while (m9ec < w6d) {
      g7 += gvs;
      m9ec = m9ec + 1;
      gvs = gvs * m;
  }
}