int main1(){
  int m3e, gc, l84, s, y, esb;
  m3e=1+25;
  gc=1;
  l84=0;
  s=0;
  y=gc;
  esb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l84 == s;
  loop invariant y == 1 + s*(s+1)/2;
  loop invariant esb == 0;
  loop invariant s <= m3e;
  loop invariant 0 <= s;
  loop assigns l84, s, y;
*/
while (1) {
      if (!(s<=m3e-1)) {
          break;
      }
      l84 = l84 + 1;
      s++;
      y += l84;
      y += esb;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s <= y;
  loop invariant gc - s == -25;
  loop invariant gc == s - 25;
  loop invariant s*s + s - 2*m3e == 650;
  loop invariant 0 <= s <= y;
  loop invariant gc >= 1;
  loop invariant m3e >= 26;
  loop assigns gc, s, m3e;
*/
while (s<y) {
      gc++;
      s++;
      m3e = m3e + s;
  }
}