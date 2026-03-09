int main1(int v,int s){
  int dd8, m6ii, gjj, ya;
  dd8=s*2;
  m6ii=1;
  gjj=0;
  ya=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ya == v + 2 * gjj;
  loop invariant s == \at(s, Pre) - 2 + 2 * m6ii;
  loop invariant dd8 == 2 * \at(s, Pre);
  loop invariant 0 <= gjj;
  loop invariant m6ii >= 1;
  loop invariant s == (dd8/2) - 2 + 2*m6ii;
  loop assigns m6ii, ya, gjj, s;
*/
while (m6ii<dd8) {
      m6ii = 2*m6ii;
      ya += 2;
      gjj = gjj + 1;
      s = s + m6ii;
  }
}