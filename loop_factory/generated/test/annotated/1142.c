int main1(){
  int r5n, r, bx, nfkt, z3wx;
  r5n=0;
  r=0;
  bx=0;
  nfkt=(1%18)+5;
  z3wx=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == r5n;
  loop invariant r == bx;
  loop invariant z3wx == -1 + 21*(r/7) + ((r%7) * ((r%7) + 1)) / 2;
  loop invariant nfkt == 6 - r;
  loop invariant z3wx >= -1;
  loop invariant r <= 6;
  loop assigns r, r5n, bx, nfkt, z3wx;
*/
while (nfkt>0) {
      r = r+1*1;
      r5n = r5n+1*1;
      bx = bx+1*1;
      nfkt--;
      z3wx = z3wx+(r%7);
  }
}