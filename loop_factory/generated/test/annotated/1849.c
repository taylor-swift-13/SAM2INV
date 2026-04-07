int main1(int d){
  int ls, y53, sp, dlyf, l, r6, ux, r, mxgn, sz5;
  ls=68;
  y53=0;
  sp=0;
  dlyf=0;
  l=0;
  r6=0;
  ux=0;
  r=0;
  mxgn=ls;
  sz5=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sp + dlyf + l + r6 == y53;
  loop invariant sp >= 0;
  loop invariant dlyf >= 0;
  loop invariant l >= 0;
  loop invariant r6 >= 0;
  loop invariant sp == (y53 + 10) / 11;
  loop invariant 0 <= y53 <= ls + (d % 7);
  loop invariant mxgn >= ls + 2*sz5*y53;
  loop invariant ux == sp + 2*dlyf + 3*l + 4*r6;
  loop invariant 0 <= r <= 7 * y53;
  loop assigns sp, ux, dlyf, l, r6, y53, mxgn, r;
*/
while (y53<ls+(d%7)) {
      if (y53%11==0) {
          sp += 1;
          ux = ux + 1;
      }
      else {
          if (y53%8==0) {
              dlyf += 1;
              ux += 2;
          }
          else {
              if (y53%6==0) {
                  l = l + 1;
                  ux = ux + 3;
              }
              else {
                  if (1) {
                      r6 = r6 + 1;
                      ux += 4;
                  }
              }
          }
      }
      y53 = y53 + 1;
      mxgn = mxgn + sp;
      r = r+y53%8;
      mxgn = mxgn+sz5+sz5;
  }
}