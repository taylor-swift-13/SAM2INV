int main1(){
  int b3, f0h, vg, b, q;
  b3=157;
  f0h=0;
  vg=0;
  b=0;
  q=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= f0h;
  loop invariant f0h <= b3;
  loop invariant f0h == vg;
  loop invariant 2*b == (f0h*(f0h + 1));
  loop invariant 6 * (q - 10) == (f0h * (f0h - 1) * (f0h - 2));
  loop assigns q, f0h, b, vg;
*/
while (f0h < b3) {
      q = (q + (b)+(-(vg)));
      f0h += 1;
      b += f0h;
      vg += 1;
  }
}