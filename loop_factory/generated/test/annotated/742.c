int main1(){
  int so, d8, b2, okm;
  so=40;
  d8=0;
  b2=(1%28)+10;
  okm=so;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d8 >= 0;
  loop invariant b2 >= 0;
  loop invariant okm == so + d8 * b2 + ((d8 - 1) * d8 * (2 * d8 - 1)) / 6;
  loop invariant b2 == 11 - d8*(d8 - 1)/2;
  loop invariant so == 40;
  loop assigns b2, d8, okm;
*/
while (b2>d8) {
      b2 -= d8;
      d8 = d8 + 1;
      okm += b2;
  }
}