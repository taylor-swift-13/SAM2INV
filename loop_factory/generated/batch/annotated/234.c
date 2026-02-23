int main1(int a,int k){
  int j, h, y;

  j=a-3;
  h=0;
  y=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == h*(h+1)/2;
  loop invariant j == \at(a, Pre) - 3;

  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant h >= 0;
  loop invariant y == (h*(h+1))/2;
  loop invariant 0 <= h;
  loop invariant (h <= j) || (j < 0);
  loop assigns y, h;
*/
while (h<=j-1) {
      y = y+1;
      y = y+h;
      h = h+1;
  }

}
