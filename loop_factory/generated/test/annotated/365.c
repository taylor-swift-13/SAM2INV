int main1(int u){
  int fke, bds, e, c, g5fb;
  fke=(u%38)+18;
  bds=2;
  e=0;
  c=(u%28)+10;
  g5fb=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g5fb <= -5;
  loop invariant bds == 2;
  loop invariant e >= 0;
  loop invariant fke == (\at(u, Pre) % 38) + 18;
  loop invariant u == \at(u, Pre) + e*(fke - bds);
  loop invariant c == ((\at(u, Pre) % 28) + 10) - e*(e-1)/2;
  loop assigns c, e, u, g5fb;
*/
while (1) {
      if (!(c>e)) {
          break;
      }
      c = c - e;
      e += 1;
      u = u+fke-bds;
      g5fb += 1;
      g5fb = (3)+(g5fb*3);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fke == (\at(u, Pre) % 38) + 18;
  loop invariant bds > 0;
  loop assigns bds, c, u;
*/
while (bds>c) {
      bds = bds - c;
      c = c + 1;
      u = (c)+(u);
  }
}