int main1(int a,int k){
  int d, j, v, m;

  d=77;
  j=0;
  v=d;
  m=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == d + 3*j;
  loop invariant j <= d;
  loop invariant j >= 0;
  loop invariant v >= d;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v == 77 + 3*j;
  loop invariant 0 <= j;
  loop invariant d == 77;
  loop assigns v, j;
*/
while (1) {
      if (j>=d) {
          break;
      }
      v = v+3;
      j = j+1;
  }

}
