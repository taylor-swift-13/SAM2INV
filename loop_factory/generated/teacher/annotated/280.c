int main1(int b,int k){
  int j, n, l;

  j=b-5;
  n=0;
  l=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= 0;

  loop invariant l <= -3;
  loop invariant l % 3 == 0;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == b - 5;
  loop invariant 0 <= n;
  loop invariant (l % 3) == 0;

  loop invariant j == \at(b, Pre) - 5;
  loop invariant j < 0 || n <= j;

  loop invariant l < 0;
  loop assigns l, n;
*/
while (n<j) {
      if ((n%6)==0) {
          l = l+l;
      }
      n = n+1;
  }

}
