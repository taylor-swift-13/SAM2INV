int main1(int y,int c){
  int w, bs, z2c;
  w=34;
  bs=0;
  z2c=bs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z2c == 2 * bs;
  loop invariant y == \at(y, Pre) + bs * (w + 4);
  loop invariant c == \at(c, Pre);
  loop invariant 0 <= bs;
  loop invariant bs <= w;
  loop invariant y == \at(y, Pre) + 38*bs;
  loop invariant w == 34;
  loop invariant z2c <= 2 * w;
  loop assigns z2c, bs, y;
*/
while (bs<w) {
      z2c += 2;
      bs = bs + 1;
      y = y + w;
      y += 4;
  }
}