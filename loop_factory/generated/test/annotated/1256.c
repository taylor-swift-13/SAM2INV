int main1(){
  int hb, jgl, w0b, g41a, z5, ng3, z, ky;
  hb=1;
  jgl=hb;
  w0b=1;
  g41a=0;
  z5=2;
  ng3=jgl;
  z=0;
  ky=hb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g41a == (w0b - 1) * (w0b - 1);
  loop invariant z == (w0b - 1) * (w0b + 2) / 2;
  loop invariant ky >= 1;
  loop invariant ng3 >= 1;
  loop assigns g41a, ng3, w0b, z, ky;
*/
while (w0b<=hb) {
      g41a = g41a+2*w0b-1;
      ng3 = ng3+(g41a%5);
      w0b++;
      z = z + w0b;
      ky = ky + jgl;
      ky = ky*ky+z5;
  }
}