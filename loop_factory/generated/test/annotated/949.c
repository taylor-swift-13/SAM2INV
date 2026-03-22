int main1(){
  int xb, l06w, tqc, zl, h;
  xb=1;
  l06w=0;
  tqc=0;
  zl=l06w;
  h=xb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zl == (xb + 2*h) * l06w;
  loop invariant 0 <= l06w;
  loop invariant l06w <= xb;
  loop invariant 0 <= tqc;
  loop invariant tqc <= xb;
  loop invariant zl == 2*h*l06w + tqc;
  loop invariant h == xb;
  loop assigns tqc, zl, l06w;
*/
while (1) {
      if (!(!(tqc+3<=xb))) {
          tqc = tqc + 3;
      }
      else {
          tqc = xb;
      }
      zl += tqc;
      zl = zl+h+h;
      l06w += 1;
      if (l06w>=xb) {
          break;
      }
  }
}