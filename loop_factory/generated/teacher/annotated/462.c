int main1(int k,int q){
  int r, c, j;

  r=q+10;
  c=0;
  j=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j == 0) || (j == r);
  loop invariant r == q + 10;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j == 0 || j == q + 10;
  loop invariant j == \at(q, Pre) + 10 || j == 0;
  loop invariant j == 0 || j == r;
  loop invariant r == \at(q, Pre) + 10;
  loop invariant j == q + 10 || j == 0;
  loop assigns j;
*/
while (1) {
      j = j+4;
      j = j-j;
  }

}
