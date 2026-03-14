int main1(int y){
  int lqf, v, cj, g9, ga, hw;
  lqf=128;
  v=lqf;
  cj=0;
  g9=-1;
  ga=0;
  hw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hw == g9*(g9+1)/2;
  loop invariant cj == y*(g9+1);
  loop invariant ga == 0;
  loop invariant (lqf == 128);
  loop invariant (-1 <= g9);
  loop invariant (g9 <= lqf);
  loop assigns g9, cj, ga, hw;
*/
while (g9<=lqf-1) {
      g9++;
      cj = cj + y;
      ga = ga*4;
      hw += g9;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= hw;
  loop invariant lqf == 128 + y*(v - 128);
  loop invariant cj == (g9 + 1) * y + (v - 128) * (hw - g9);
  loop invariant cj == 129 * y + (v - 128) * (hw - g9);
  loop invariant ga <= 2 * (v - 128);
  loop assigns cj, v, lqf, ga;
*/
while (v<hw) {
      cj = cj+hw-g9;
      v++;
      lqf = lqf + y;
      ga = ga+(lqf%3);
  }
}