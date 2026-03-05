int main1(int g,int c){
  int tv9s, y1;
  tv9s=67;
  y1=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y1 - 1) % 3 == 0;
  loop invariant y1 <= tv9s + 3;
  loop invariant c == \at(c, Pre);
  loop invariant g == \at(g, Pre);
  loop invariant tv9s == 67;
  loop invariant 1 <= y1;
  loop assigns y1;
*/
while (y1<=tv9s) {
      y1 += 1;
      y1 += 2;
  }
}