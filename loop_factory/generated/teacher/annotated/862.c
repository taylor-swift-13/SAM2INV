int main1(int a,int k){
  int d, j, v, m;

  d=77;
  j=0;
  v=d;
  m=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j <= d;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant d == 77;
  loop invariant m == 77;
  loop invariant v == d + j*(m+m);
  loop invariant a == \at(a,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant j >= 0;
  loop invariant v == 77 + j*(m + m);
  loop invariant v == d + 2*m*j;
  loop invariant m == d;
  loop invariant v == d * (2 * j + 1);
  loop invariant 0 <= j;
  loop invariant v == d + j * (2 * m);
  loop invariant 0 <= j && j <= d;
  loop invariant v == d + j*(2*m);
  loop invariant v <= d + d*(2*m);
  loop assigns v, j;
*/
while (j<d) {
      v = v+m+m;
      j = j+1;
  }

}
