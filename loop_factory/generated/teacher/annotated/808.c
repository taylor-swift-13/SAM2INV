int main1(int m,int p){
  int n, j, w, y;

  n=66;
  j=0;
  w=5;
  y=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant n == 66;
  loop invariant j >= 0;
  loop invariant w == 5 + (j * (j - 1)) / 2;
  loop invariant y >= 5;
  loop invariant w == 5 + j*(j-1)/2;
  loop invariant y > 0;
  loop invariant w >= j;
  loop invariant w >= 5;
  loop assigns w, y, j;
*/
while (1) {
      w = w+j;
      y = y*y;
      y = y+w*y;
      j = j+1;
  }

}
