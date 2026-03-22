int main1(){
  int i5, wt, g, akz;
  i5=1+19;
  wt=0;
  g=0;
  akz=i5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == wt;
  loop invariant akz == i5 + (g * (g + 1)) / 2;
  loop invariant 0 <= wt <= i5;
  loop invariant i5 == 20;
  loop assigns wt, g, akz;
*/
while (g<i5) {
      wt++;
      g++;
      akz = akz + g;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wt <= akz;
  loop invariant i5 >= wt;
  loop invariant i5 >= 20;
  loop invariant wt >= 1;
  loop invariant g >= 1;
  loop invariant akz >= 1;
  loop assigns i5, akz, g;
*/
while (wt*2<=akz) {
      i5 = i5 + g;
      akz = ((wt*2))+(-(1));
      if (wt+3<=i5+akz) {
          g = g*g;
      }
  }
}