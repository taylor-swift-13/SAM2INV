int main1(int a,int q){
  int n, v, j;

  n=q;
  v=0;
  j=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a,Pre);
  loop invariant n == q;
  loop invariant j >= q;
  loop invariant (j - q) % 4 == 0;
  loop invariant q == \at(q, Pre);
  loop assigns j;
*/
while (1) {
      j = j+3;
      j = j+1;
  }

}
