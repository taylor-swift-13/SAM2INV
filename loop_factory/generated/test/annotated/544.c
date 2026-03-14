int main1(int g){
  int nk4e, y, c, rj;
  nk4e=g-7;
  y=0;
  c=0;
  rj=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rj == 7 - y;
  loop invariant g == \at(g, Pre) + y * nk4e;
  loop invariant c == y * (15 - y) / 2;
  loop invariant nk4e == \at(g, Pre) - 7;
  loop invariant 0 <= y <= 7;
  loop assigns c, y, rj, g;
*/
while (1) {
      if (!(y<nk4e&&rj>0)) {
          break;
      }
      c += rj;
      y++;
      rj -= 1;
      g += nk4e;
  }
}