int main1(){
  int zz, v7b, lj8f, s0w, dw;
  zz=(1%12)+11;
  v7b=0;
  lj8f=v7b;
  s0w=lj8f;
  dw=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lj8f == 4 * v7b;
  loop invariant dw == 3 + v7b * (v7b + 1) / 2;
  loop invariant s0w == 0;
  loop invariant s0w <= lj8f;
  loop invariant (0 <= v7b && v7b <= zz);
  loop assigns v7b, s0w, dw, lj8f;
*/
while (v7b < zz) {
      v7b++;
      if (lj8f < s0w) {
          s0w = lj8f;
      }
      dw = dw + v7b;
      lj8f += 4;
  }
}