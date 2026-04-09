int main1(int x){
  int yd, avcw, z0e;
  yd=x-8;
  avcw=0;
  z0e=avcw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (z0e == 0);
  loop invariant (avcw >= 0);
  loop invariant x == \at(x, Pre) + 2*avcw;
  loop invariant yd == \at(x, Pre) - 8;
  loop invariant (avcw <= yd) || (avcw == 0);
  loop assigns x, z0e, avcw;
*/
while (avcw < yd) {
      x += 2;
      z0e = z0e + z0e;
      avcw++;
  }
}