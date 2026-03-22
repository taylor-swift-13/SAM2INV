int main1(){
  int kt, bg, iq, h3, wss, f3b;
  kt=1;
  bg=kt;
  iq=0;
  h3=0;
  wss=11;
  f3b=bg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h3 == iq;
  loop invariant f3b == 1 + 11 * iq + iq * (iq + 1) / 2;
  loop invariant h3 <= kt;
  loop invariant bg == 1;
  loop invariant kt == 1;
  loop invariant h3 >= 0;
  loop invariant wss == 11 + bg * h3;
  loop assigns wss, iq, h3, f3b;
*/
while (1) {
      if (!(h3<=kt-1)) {
          break;
      }
      wss = wss + bg;
      iq += 1;
      h3 += 1;
      f3b = f3b + wss;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f3b - h3 == 12;
  loop invariant bg == 1;
  loop invariant iq == 1;
  loop invariant kt == h3;
  loop invariant h3 >= 1;
  loop assigns f3b, kt, h3;
*/
while (1) {
      if (!(h3<bg)) {
          break;
      }
      f3b += 1;
      kt += iq;
      h3 += 1;
  }
}