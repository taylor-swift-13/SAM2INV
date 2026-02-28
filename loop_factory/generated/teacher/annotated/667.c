int main1(int m,int n){
  int j, b, v, a;

  j=m;
  b=0;
  v=n;
  a=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant v == n + 2*b;
  loop invariant a - j == b*(b-1)/2;
  loop invariant j == \at(m,Pre);
  loop invariant v == \at(n,Pre) + 2*b;
  loop invariant a == \at(m,Pre) + b*(b-1)/2;

  loop invariant j == m;
  loop invariant 0 <= b;

  loop invariant a == j + (b*(b-1))/2;

  loop invariant a == j + b*(b-1)/2;
  loop assigns v, b, a;
*/
while (1) {
      if (b>=j) {
          break;
      }
      v = v+1;
      b = b+1;
      v = v+1;
      a = a-1;
      a = a+b;
  }

}
