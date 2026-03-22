int main1(int z,int w){
  int vipy, jbxb, l9, l4y, u, bh8, m, cx;
  vipy=122;
  jbxb=0;
  l9=0;
  l4y=vipy;
  u=5;
  bh8=-4;
  m=4;
  cx=vipy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l9 + l4y == vipy;
  loop invariant z == \at(z,Pre) + l9 * jbxb;
  loop invariant w == \at(w,Pre) + l9 * (vipy - jbxb + 7);
  loop invariant 0 <= l9 <= vipy;
  loop invariant 0 <= l4y <= vipy;
  loop invariant vipy == 122;
  loop invariant jbxb == 0;
  loop invariant m == 4;
  loop invariant bh8 == -4;
  loop assigns l4y, l9, u, z, cx, w;
*/
while (1) {
      if (!(l9<vipy&&l4y>0)) {
          break;
      }
      l4y = l4y - 1;
      l9 = l9 + 1;
      if (u+6<vipy) {
          u = u + cx;
      }
      if (jbxb+3<=vipy+vipy) {
          z += jbxb;
      }
      cx += 2;
      w = w+vipy-jbxb;
      cx = u+bh8+m;
      u = u + 1;
      if (jbxb+1<=l9+vipy) {
          w += 1;
      }
      w += 6;
  }
}