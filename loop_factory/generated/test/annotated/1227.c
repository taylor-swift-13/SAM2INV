int main1(int c){
  int xh, nf, eg, o, lmk;
  xh=48;
  nf=c;
  eg=0;
  o=-2;
  lmk=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= lmk <= xh+1;
  loop invariant 2*c == 2*\at(c, Pre) + (lmk - 1)*(lmk + 2);
  loop invariant nf == \at(c, Pre) + (lmk - 2)*(lmk - 1)*(lmk - 4);
  loop invariant eg == 3*(lmk - 1)*(lmk - 1) - 5*(lmk - 1);
  loop invariant o == 6*lmk - 8;
  loop assigns c, nf, eg, o, lmk;
*/
while (lmk<=xh) {
      nf += eg;
      eg = eg + o;
      o += 6;
      lmk = lmk + 1;
      c += lmk;
  }
}