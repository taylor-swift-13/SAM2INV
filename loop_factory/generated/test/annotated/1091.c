int main1(int w){
  int q, yly9, y49a, ml6, p4, h3w;
  q=(w%40)+8;
  yly9=3;
  y49a=0;
  ml6=(w%28)+10;
  p4=q;
  h3w=yly9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h3w == 3 + y49a;
  loop invariant p4 == q + 3*y49a;
  loop invariant ml6 == ((\at(w, Pre) % 28) + 10) - y49a*(y49a - 1)/2;
  loop invariant y49a >= 0;
  loop invariant w - \at(w, Pre) == y49a*(q - yly9);
  loop assigns ml6, h3w, w, y49a, p4;
*/
while (1) {
      if (!(ml6>y49a)) {
          break;
      }
      ml6 = ml6 - y49a;
      h3w++;
      w = w+q-yly9;
      y49a = y49a + 1;
      p4 = (3)+(p4);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h3w >= 3;
  loop invariant yly9 >= 3;
  loop invariant h3w - y49a == 3;
  loop assigns ml6, y49a, h3w, yly9, w;
*/
while (1) {
      if (!(ml6>0)) {
          break;
      }
      y49a = y49a+w*w;
      yly9 = yly9+w*w;
      h3w = h3w+w*w;
      ml6 -= 1;
      w = w+(y49a%9);
  }
}