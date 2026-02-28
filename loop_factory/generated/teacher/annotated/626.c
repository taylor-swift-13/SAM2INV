int main1(int b,int n){
  int l, j, f, i, e;

  l=b+19;
  j=0;
  f=1;
  i=l;
  e=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == j + 1;
  loop invariant j >= 0;
  loop invariant l == \at(b, Pre) + 19;
  loop invariant l == b + 19;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);

  loop assigns f, j;
*/
while (1) {
      if (j>=l) {
          break;
      }
      f = f+1;
      j = j+1;
  }

}
