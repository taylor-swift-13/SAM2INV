int main1(int m,int n){
  int x, l, j;

  x=76;
  l=x;
  j=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;
  loop invariant l >= 0 && l <= 76 && x == 76 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= l;
  loop invariant l <= 76;
  loop invariant (0 <= l) && (l <= 76);
  loop invariant l >= 0;
  loop invariant x == 76;
  loop assigns j, l;
*/
while (l>0) {
      j = j+j;
      l = l-1;
  }

}
