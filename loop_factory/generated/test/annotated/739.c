int main1(){
  int y4, us, fu;
  y4=0;
  us=(1%28)+10;
  fu=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fu == 4 + ((y4 + 1) / 2);
  loop invariant y4 >= 0;
  loop invariant us + y4*(y4 - 1)/2 == 11;
  loop assigns fu, us, y4;
*/
while (us>y4) {
      us = us - y4;
      y4 += 1;
      fu = fu+(y4%2);
  }
}