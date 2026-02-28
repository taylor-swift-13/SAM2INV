int main1(int a,int p){
  int k, u, y;

  k=a-9;
  u=0;
  y=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (a == \at(a, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (y == 0) || (y == 6);
  loop invariant 0 <= y <= 6;
  loop invariant k == a - 9;
  loop invariant y == 0 || y == 6;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop assigns y;
*/
while (1) {
      y = y+2;
      y = y-y;
  }

}
