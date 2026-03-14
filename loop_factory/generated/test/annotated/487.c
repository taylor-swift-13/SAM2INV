int main1(){
  int r, d, f, ag7, cz8, j1n, kn58;
  r=54;
  d=r+6;
  f=0;
  ag7=0;
  cz8=0;
  j1n=(1%18)+5;
  kn58=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ag7 + j1n == 6;
  loop invariant f == ag7;
  loop invariant 0 <= j1n <= 6;
  loop invariant 0 <= f <= 6;
  loop invariant kn58 >= 60;
  loop invariant cz8 == f;
  loop invariant (kn58 % 4) == ((ag7) % 5) % 4;
  loop assigns cz8, f, ag7, j1n, kn58;
*/
while (j1n>=1) {
      cz8 = cz8+1*1;
      f = f+1*1;
      ag7 = ag7+1*1;
      j1n -= 1;
      kn58 = kn58*4+(ag7%5)+0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f >= 0;
  loop invariant ag7 >= 0;
  loop invariant d >= 60;
  loop invariant ag7 + d <= 66;
  loop assigns ag7, d, f;
*/
while (ag7>d) {
      ag7 -= d;
      d++;
      f = (d)+(f);
      f = f%5;
  }
}