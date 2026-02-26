int main1(int a,int k){
  int m, j, e, v;

  m=22;
  j=0;
  e=-6;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == j - 6;
  loop invariant v == k + j*(j-1)/2;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j <= m;
  loop invariant v == \at(k, Pre) + j*(j-1)/2;
  loop invariant j >= 0;
  loop invariant v == k + (j*(j-1))/2;
  loop invariant e == -6 + j;
  loop invariant v == \at(k, Pre) + ((j - 1) * j) / 2;
  loop assigns e, v, j;
*/
while (j<=m-1) {
      e = e+1;
      v = v+e;
      v = v+5;
      j = j+1;
  }

}
