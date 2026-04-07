int main1(){
  int lkon, x9, th9, ac, p, wnng, xv8t, vjva;
  lkon=1;
  x9=0;
  th9=x9;
  ac=lkon;
  p=lkon;
  wnng=lkon;
  xv8t=x9;
  vjva=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x9 <= lkon;
  loop invariant p == x9 + 1;
  loop invariant th9 == x9 / 2;
  loop invariant ac == 1 + ((x9 + 1) / 2);
  loop invariant xv8t == x9 / 9;
  loop invariant vjva == -3 + (x9/2)*((x9/2) + 3) + ((x9) % 2)*((x9/2) + 2);
  loop invariant wnng == 1 + 4 * x9 + x9 * (x9 - 1) / 2;
  loop invariant lkon == 1;
  loop assigns x9, th9, ac, xv8t, p, wnng, vjva;
*/
while (1) {
      if (!(x9 < lkon)) {
          break;
      }
      x9 = x9 + 1;
      if ((x9 % 2) == 0) {
          th9++;
      }
      else {
          ac++;
      }
      if ((x9%9)==0) {
          xv8t += 1;
      }
      p++;
      wnng += 2;
      vjva += ac;
      wnng += p;
  }
}