int main1(int b,int k){
  int i, t, n, v;

  i=b;
  t=0;
  n=b;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n <= i;
  loop invariant i == b;
  loop invariant v == b;
  loop invariant n >= b;
  loop invariant (n - b) % (1 + 2*b) == 0;
  loop invariant v == i;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant i == v;
  loop assigns n;
*/
while (n<i) {
      if (n<i) {
          n = n+1;
      }
      n = n+v+v;
  }

}
