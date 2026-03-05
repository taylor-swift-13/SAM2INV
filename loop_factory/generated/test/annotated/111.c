int main1(){
  int l0, w5x, ho;
  l0=1+6;
  w5x=0;
  ho=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w5x >= 0;
  loop invariant l0 == 1 + 6 && 0 <= ho && ho <= l0 && (ho == 0 || ho == 1);
  loop invariant w5x >= 0 && (ho == 0 ==> w5x == 0);
  loop invariant w5x >= ho;
  loop assigns ho, w5x;
*/
while (ho>0&&ho<=l0) {
      if (ho>ho) {
          ho = ho - ho;
      }
      else {
          ho = 0;
      }
      ho += 1;
      w5x++;
  }
}