int main1(){
  int b, i, e8, wy9;
  b=1+14;
  i=0;
  e8=0;
  wy9=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e8 == ((i * (15 - i)) / 2);
  loop invariant wy9 == 7 - i;
  loop invariant i <= b;
  loop invariant i >= 0;
  loop assigns e8, i, wy9;
*/
while (i<b&&wy9>0) {
      e8 = e8 + wy9;
      i = i + 1;
      wy9--;
  }
}