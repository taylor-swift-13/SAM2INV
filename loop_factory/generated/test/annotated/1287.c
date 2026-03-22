int main1(int b,int q){
  int y, c0wh;
  y=84;
  c0wh=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant -3 <= c0wh <= y;
  loop invariant (b == \at(b, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant y == 84;
  loop assigns c0wh;
*/
for (; c0wh+1<=y; c0wh++) {
  }
}