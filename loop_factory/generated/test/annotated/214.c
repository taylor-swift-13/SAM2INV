int main1(int c,int l){
  int a5, ry;
  a5=38;
  ry=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ry % 2 == 1;
  loop invariant ry <= 2 * a5 + 1;
  loop invariant c == \at(c, Pre);
  loop invariant l == \at(l, Pre);
  loop invariant a5 == 38;
  loop invariant 1 <= ry;
  loop assigns ry;
*/
while (ry<=a5) {
      ry = ry + ry;
      ry++;
  }
}