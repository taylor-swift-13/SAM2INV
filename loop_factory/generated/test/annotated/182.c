int main1(int y){
  int y4u2, a9, eig;
  y4u2=y;
  a9=1;
  eig=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a9 == 1;
  loop invariant y4u2 == \at(y, Pre);
  loop invariant eig >= -3;
  loop invariant y >= y4u2;
  loop assigns eig, y;
*/
while (a9<=y4u2/2) {
      eig = eig + 1;
      eig = eig+eig*eig;
      y += y4u2;
  }
}