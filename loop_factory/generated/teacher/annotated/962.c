int main1(int k,int q){
  int p, l, v;

  p=k+5;
  l=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == k + 5;
  loop invariant v >= k + 5;
  loop invariant p == k + 5 && v >= p;
  loop invariant v >= p;
  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant k == \at(k, Pre) && q == \at(q, Pre);
  loop invariant p == k + 5 && v >= k + 5;
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v*v;
  }

}
