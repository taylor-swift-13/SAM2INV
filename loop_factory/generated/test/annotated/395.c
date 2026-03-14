int main1(){
  int m, j7e, b, a, tt98;
  m=79;
  j7e=0;
  b=20;
  a=1;
  tt98=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == j7e + 1;
  loop invariant j7e == tt98;
  loop invariant b >= 0;
  loop invariant a <= m + 1;
  loop assigns a, b, j7e, tt98;
*/
while (b>0&&a<=m) {
      if (b>a) {
          b = b - a;
      }
      else {
          b = 0;
      }
      tt98 = tt98 + 1;
      j7e++;
      a++;
  }
}