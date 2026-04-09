int main1(){
  int k86, j, le, ct3, xq, g3a7;
  k86=(1%40)+16;
  j=0;
  le=j;
  ct3=0;
  xq=0;
  g3a7=k86;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ct3 == le * j);
  loop invariant (0 <= j);
  loop invariant (j <= k86);
  loop invariant le == 0;
  loop invariant g3a7 >= k86;
  loop invariant g3a7 <= k86 + 3 * j;
  loop invariant xq >= j * k86;
  loop invariant k86 == (1 % 40) + 16;
  loop assigns ct3, xq, j, g3a7;
*/
while (j < k86) {
      ct3 = ct3 + le;
      xq += g3a7;
      j++;
      g3a7 = g3a7+(xq%4);
  }
}