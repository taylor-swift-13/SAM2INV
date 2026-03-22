int main1(){
  int q9, ld2, x, pl3;
  q9=(1%28)+8;
  ld2=(1%22)+5;
  x=0;
  pl3=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= 0;
  loop invariant 0 <= ld2 <= 6;
  loop invariant (pl3 == -3) || (pl3 >= 0);
  loop invariant (q9 % 9) == 0;
  loop invariant ld2 * q9 <= 54;
  loop invariant q9 >= 9;
  loop assigns ld2, x, q9, pl3;
*/
while (ld2!=0) {
      if (ld2%2==1) {
          x += q9;
          ld2--;
      }
      q9 = 2*q9;
      ld2 = ld2/2;
      pl3 += x;
      pl3 = (pl3)+(pl3*pl3);
  }
}