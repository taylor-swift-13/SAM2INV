int main1(){
  int ixv, sg, x, oky;
  ixv=(1%16)+17;
  sg=0;
  x=0;
  oky=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sg == x % 4;
  loop invariant oky == x * (x + 3) / 2;
  loop invariant x <= ixv;
  loop invariant 0 <= x;
  loop assigns x, sg, oky;
*/
while (x<ixv) {
      x = x + 1;
      sg = (sg+1)%4;
      oky += x;
      oky = oky + 1;
  }
}