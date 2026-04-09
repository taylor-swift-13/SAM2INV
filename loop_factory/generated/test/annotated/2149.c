int main1(){
  int n5, d3, r6, i;
  n5=(1%30)+8;
  d3=0;
  r6=0;
  i=d3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= d3 && d3 <= n5;
  loop invariant r6 == (d3 * (d3 * d3 - 1)) / 6;
  loop invariant i == d3 + ((d3 - 1) * d3 * (d3 + 1) * (d3 + 2)) / 24;
  loop invariant 6 * r6 == (d3 * (d3 - 1) * (d3 + 1));
  loop invariant 24 * i == ((d3 * d3 * d3 * d3) + 2 * d3 * d3 * d3 - d3 * d3 + 22 * d3);
  loop invariant r6 >= 0 && i >= 0;
  loop invariant (24 * i == d3 * d3 * d3 * d3 + 2 * d3 * d3 * d3 - d3 * d3 + 22 * d3);
  loop invariant r6 == (d3 * (d3 - 1) * (d3 + 1)) / 6;
  loop invariant i == (d3 * (d3 - 1) * (d3 + 1) * (d3 + 2)) / 24 + d3;
  loop invariant (6 * r6) == (d3 * (d3 - 1) * (d3 + 1));
  loop invariant (24 * i) == (24 * d3 + d3 * (d3 - 1) * (d3 + 1) * (d3 + 2));
  loop assigns d3, r6, i;
*/
while (d3 < n5) {
      r6 = r6 + (d3 * (d3 + 1)) / 2;
      d3++;
      i = (r6)+(i);
      i = i + 1;
  }
}