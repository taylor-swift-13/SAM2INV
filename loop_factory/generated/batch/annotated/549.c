int main1(int b,int n){
  int k, i, v, d;

  k=67;
  i=0;
  v=k;
  d=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant k == 67;
  loop invariant i >= 0;
  loop invariant v > 0;
  loop invariant (i >= 0);
  loop invariant (k == 67);
  loop invariant (b == \at(b, Pre));
  loop invariant (n == \at(n, Pre));
  loop invariant (v >= 67);
  loop invariant (v % 67 == 0);
  loop invariant v >= 67;
  loop invariant v % 67 == 0;
  loop invariant v >= k;
  loop invariant (i == 0) ==> (v == 67);
  loop invariant (i > 0) ==> (v > 67 && v % 2 == 0);
  loop assigns v, i;
*/
while (1) {
      v = v*2;
      i = i+1;
  }

}
