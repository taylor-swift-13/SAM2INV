int main1(int h){
  int g9, zn7, rh, t, c1e, di2;
  g9=h;
  zn7=0;
  rh=g9;
  t=20;
  c1e=h;
  di2=(h%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c1e == g9;
  loop invariant h == \at(h, Pre);
  loop invariant g9 == \at(h, Pre);
  loop invariant di2 == (\at(h, Pre) % 6) + 2;
  loop invariant t >= 20;
  loop invariant rh >= h;
  loop invariant zn7 == 0;
  loop assigns rh, t, h, c1e;
*/
while (1) {
      if (!(c1e<g9)) {
          break;
      }
      rh = rh*di2+h;
      t = t*di2;
      h = h + zn7;
      c1e = g9;
  }
}