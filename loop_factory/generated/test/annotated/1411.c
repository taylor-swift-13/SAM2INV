int main1(int m){
  int r9cs, ul3, q8, xxa;
  r9cs=19;
  ul3=0;
  q8=m;
  xxa=r9cs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xxa - q8 == r9cs - m;
  loop invariant ul3 == 0 || ul3 == r9cs;
  loop invariant 0 <= ul3;
  loop invariant ul3 <= r9cs;
  loop invariant q8 >= m;
  loop assigns q8, xxa, ul3;
*/
while (ul3<=r9cs-1) {
      q8++;
      xxa = (1)+(xxa);
      ul3 = r9cs;
  }
}