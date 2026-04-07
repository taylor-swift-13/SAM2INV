int main1(){
  int f9ia, l8, gnos, biy, hf5;
  f9ia=1*5;
  l8=0;
  gnos=l8;
  biy=8;
  hf5=l8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gnos == l8 * l8;
  loop invariant biy == l8 * l8 + 8;
  loop invariant l8 <= f9ia;
  loop invariant hf5 == l8 * l8;
  loop invariant 0 <= l8;
  loop assigns l8, gnos, hf5, biy;
*/
while (l8 < f9ia) {
      l8 += 1;
      gnos = gnos + (2*l8 - 1);
      hf5 = hf5 + (2*l8 - 1);
      biy = biy + (2*l8 - 1);
  }
}