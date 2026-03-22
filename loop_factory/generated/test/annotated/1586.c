int main1(int a){
  int an, zl, o3, zx, wk, oe, o3v, jk, h, xl, dr;
  an=59;
  zl=2;
  o3=0;
  zx=a*4;
  wk=zl;
  oe=an;
  o3v=13;
  jk=1;
  h=0;
  xl=an;
  dr=zl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o3 % 2 == 0;
  loop invariant o3 <= an + 1;
  loop invariant dr == (2 + (o3/2) * ((o3/2) + 1));
  loop invariant xl == an;
  loop invariant o3 >= 0;
  loop invariant 2 * h == a * o3;
  loop invariant 2 * (jk - 1) == o3 * (3 + a + zl);
  loop invariant 4*(dr - zl) == (o3 * (o3 + 2));
  loop invariant wk == zl;
  loop invariant ((zx == a*4) || (zx == wk));
  loop assigns o3, zx, o3v, jk, oe, dr, h;
*/
while (o3<=an-1) {
      o3 += 2;
      if (wk<=zx) {
          zx = wk;
      }
      if (o3v+3<an) {
          o3v++;
      }
      jk = jk + 3;
      oe += o3v;
      dr += o3;
      jk = jk + a;
      o3v += wk;
      h = h + a;
      jk += zl;
      if (an<xl+2) {
          o3v = o3v + jk;
      }
  }
}