int main1(int k){
  int bd87, d7o, ygu;
  bd87=k-4;
  d7o=bd87;
  ygu=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d7o <= bd87;
  loop invariant (ygu == 1) || (ygu == 2);
  loop invariant bd87 == \at(k, Pre) - 4;
  loop assigns k, d7o, ygu;
*/
while (d7o<bd87) {
      if (ygu>=7) {
          ygu = -1;
      }
      if (ygu<=3) {
          ygu = 1;
      }
      ygu = ygu + ygu;
      d7o += 1;
      k += d7o;
  }
}