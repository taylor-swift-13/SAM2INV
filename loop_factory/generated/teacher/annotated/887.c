int main1(int k,int p){
  int y, u, j;

  y=53;
  u=0;
  j=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 0;
  loop invariant y == 53;
  loop invariant j >= y;
  loop invariant (j - y) % 2 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant y == 53 && u == 0 && j >= y;
  loop invariant j % 2 == y % 2 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant u == 0 && y == 53;
  loop invariant j >= y && (j - y) % 2 == 0;
  loop invariant ((j - y) % 2) == 0;
  loop invariant k == \at(k, Pre) &&
                   p == \at(p, Pre) &&
                   y == 53 &&
                   u == 0;
  loop invariant y == 53 && u == 0 && j >= y && (j - y) % 2 == 0;
  loop assigns j;
*/
while (1) {
      j = j+2;
      j = j+u;
      if (u+2<=j+y) {
          j = j+u;
      }
  }

}
