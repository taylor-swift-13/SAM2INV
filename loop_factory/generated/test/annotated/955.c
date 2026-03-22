int main1(int r,int g){
  int qr, r2pr, rr, c;
  qr=g-9;
  r2pr=1;
  rr=qr;
  c=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*(c - 16) == 4*(rr - \at(g, Pre) + 9);
  loop invariant rr <= qr;
  loop invariant r - \at(r, Pre) >= 0;
  loop invariant 3*c - 4*rr + 4*qr == 48;
  loop invariant r2pr == 1;
  loop invariant qr == g - 9;
  loop invariant (rr - qr) % 3 == 0;
  loop invariant c - 2*r == 16 - 2 * \at(r, Pre);
  loop assigns rr, c, r;
*/
while (rr<qr) {
      rr = rr + 3;
      c += r2pr;
      r += 2;
      c = c + 3;
  }
}