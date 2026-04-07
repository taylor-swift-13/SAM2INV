int main1(){
  int a, tb8a, ix, mipx;
  a=(1%37)+8;
  tb8a=0;
  ix=0;
  mipx=tb8a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == (1 % 37) + 8;
  loop invariant ix >= 0;
  loop invariant mipx == 0;
  loop invariant tb8a + a*ix == 0;
  loop assigns tb8a, ix, mipx;
*/
while (1) {
      if (!(tb8a >= a)) {
          break;
      }
      tb8a = tb8a - a;
      ix = ix + 1;
      mipx = mipx + tb8a;
      mipx = mipx*3;
  }
}