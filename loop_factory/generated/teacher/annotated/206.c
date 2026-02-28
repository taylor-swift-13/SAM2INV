int main1(int b,int k){
  int d, m, p, s;

  d=k;
  m=2;
  p=k;
  s=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == k;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p >= k;
  loop invariant p <= d;
  loop invariant p >= d;
  loop invariant (p - d) % 2 == 0;
  loop invariant p % 2 == k % 2;
  loop invariant p <= d + 1;
  loop assigns p;
*/
while (p<d) {
      if (p<d) {
          p = p+1;
      }
      p = p+1;
  }

}
