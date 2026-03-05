int main1(int u){
  int b5;
  b5=(u%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == \at(u, Pre);
  loop invariant b5 >= (\at(u, Pre) % 18) + 5;
  loop invariant (u*u == 0) ==> b5 == (\at(u, Pre) % 18 + 5);
  loop assigns b5;
*/
while (b5>0) {
      b5 = b5+u*u;
  }
}