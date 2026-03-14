int main1(int o){
  int m6, nl, h, m5x;
  m6=o-8;
  nl=m6;
  h=0;
  m5x=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m6 == \at(o, Pre) - 8;
  loop invariant nl == m6;
  loop invariant o == \at(o, Pre) + nl * h;
  loop invariant (h > 0) ==> (m5x == m6 - h + 1);
  loop assigns o, h, m5x;
*/
while (h<m6) {
      m5x = m6-h;
      o += nl;
      h += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m6 == \at(o, Pre) - 8;
  loop invariant nl <= m6;
  loop assigns nl, o, h;
*/
while (1) {
      if (!(nl<m6)) {
          break;
      }
      nl += 1;
      o = o + m6;
      h = m6-nl;
  }
}