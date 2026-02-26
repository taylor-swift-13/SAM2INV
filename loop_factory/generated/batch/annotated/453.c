int main1(int a,int k){
  int j, h, y;

  j=a-3;
  h=0;
  y=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 0;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == a - 3;
  loop invariant y % 4 == 0;
  loop invariant y >= 0;
  loop invariant (y % 2) == 0;
  loop assigns y;
*/
while (1) {
      y = y+2;
      if ((h%6)==0) {
          y = y+y;
      }
      y = y+h;
  }

}
