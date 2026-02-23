int main1(int b){
  int k, j, r;

  k=67;
  j=k;
  r=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant j >= 0;
  loop invariant j <= 67;
  loop invariant (j % 2 == 1);
  loop invariant k == 67;
  loop invariant j >= 1;
  loop invariant j % 2 == 1;
  loop invariant 1 <= j;
  loop invariant 0 <= j;
  loop invariant j <= k;
  loop invariant j % 2 == k % 2;
  loop assigns j;
*/
while (j-2>=0) {
      j = j-2;
  }

}
