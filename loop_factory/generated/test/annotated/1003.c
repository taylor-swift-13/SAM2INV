int main1(){
  int g, d, yf, i, j;
  g=1+21;
  d=g;
  yf=37;
  i=1;
  j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (1 <= i && i <= g + 1);
  loop invariant (yf <= 37);
  loop invariant d - i == 21;
  loop invariant g == 1 + 21;
  loop invariant i == j + 1;
  loop assigns yf, i, d, j;
*/
while (1) {
      if (!(yf>0&&i<=g)) {
          break;
      }
      if (!(yf<=i)) {
          yf = 0;
      }
      else {
          yf = yf - i;
      }
      i = i + 1;
      d++;
      j++;
  }
}