int main1(int p){
  int p90, w, ky55, l1sw, lzy, x, e, fg, m;
  p90=p;
  w=0;
  ky55=w;
  l1sw=0;
  lzy=p90;
  x=w;
  e=1;
  fg=p90;
  m=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (w == 0 ==> (p == \at(p, Pre) && ky55 == 0 && l1sw == 0 && lzy == p90 && x == 0 && m == 0 && fg == p90));
  loop invariant w == 0 || w == p90;
  loop invariant p90 == \at(p, Pre);
  loop invariant 0 <= x <= 7;
  loop invariant m >= 0;
  loop invariant ky55 >= 0;
  loop invariant l1sw >= 0;
  loop invariant e == 1;
  loop invariant p == \at(p, Pre) || p == \at(p, Pre) + 2;
  loop invariant ky55 + l1sw <= 1;
  loop invariant lzy == \at(p, Pre);
  loop invariant 0 <= ky55;
  loop invariant x <= 7;
  loop invariant m <= 10;
  loop assigns w, p, ky55, l1sw, lzy, x, m, fg;
*/
while (1) {
      if (!(w<=p90-1)) {
          break;
      }
      if (w%5==3) {
          ky55++;
      }
      else {
          l1sw++;
      }
      if (w%5==4) {
          lzy = lzy + 1;
      }
      else {
      }
      m = (m+ky55)%3;
      p += 2;
      fg = (fg+ky55)%3;
      x = (x+lzy)%8;
      m = x+e+fg;
      w = p90;
  }
}