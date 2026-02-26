int main1(int a,int k){
  int d, j, v, m;

  d=77;
  j=0;
  v=d;
  m=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 77;
  loop invariant m == 77;
  loop invariant j <= d;
  loop invariant j >= 0;
  loop invariant v == 77 + (2*m + 1) * j;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v == d + j*(2*m + 1);
  loop invariant v - j*(2*m + 1) == 77;
  loop invariant 0 <= j;
  loop assigns j, v;
*/
while (j<d) {
      v = v+m+m;
      v = v+1;
      j = j+1;
  }

}
