int main1(int m,int p){
  int l3r, x58, ys, ajr, s9, tv, ren, kx, j1, o;
  l3r=m;
  x58=0;
  ys=l3r;
  ajr=-3;
  s9=-3;
  tv=x58;
  ren=0;
  kx=p;
  j1=l3r;
  o=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tv == 0;
  loop invariant o == \at(p,Pre) + 3 * x58;
  loop invariant x58 >= 0;
  loop invariant j1 == \at(m, Pre);
  loop invariant m == \at(m,Pre) + x58;
  loop invariant p == \at(p,Pre) + ren;
  loop invariant ajr == -3 + 2 * (m - \at(m,Pre));
  loop invariant m - x58 == l3r;
  loop assigns x58, ys, p, j1, ren, tv, m, ajr, o, kx, s9;
*/
while (1) {
      if (!(x58 < l3r)) {
          break;
      }
      x58++;
      if (!(!((x58 % 2) == 0))) {
          ys += p;
      }
      if ((x58 % 2) != 0) {
          s9 += p;
      }
      else {
      }
      p += ys;
      j1 = j1+s9-s9;
      ren += ys;
      tv = tv+ys-ys;
      m++;
      ajr += 2;
      o = o + 3;
      kx = kx+ys-ys;
      kx = ajr+tv+ren;
  }
}