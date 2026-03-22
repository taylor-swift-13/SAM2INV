int main1(){
  int y0lw, cx38, a, f7e;
  y0lw=1*5;
  cx38=y0lw;
  a=y0lw;
  f7e=cx38;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == y0lw + f7e * (y0lw - cx38);
  loop invariant 0 <= cx38 <= y0lw;
  loop invariant f7e == y0lw;
  loop invariant 0 <= cx38;
  loop assigns a, cx38;
*/
for (; cx38>=1; cx38 = cx38 - 1) {
      a += f7e;
  }
}