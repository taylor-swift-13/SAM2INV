int main1(int p){
  int l, k, m;

  l=p+12;
  k=0;
  m=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant k >= 0;
  loop invariant l == \at(p, Pre) + 12;
  loop invariant p == \at(p, Pre);
  loop invariant l == p + 12;
  loop invariant m >= 1;
  loop invariant k == 0 || (m % 2 == 0);
  loop invariant (k > 0) ==> (m % 2 == 0);


  loop invariant k == 0 ==> m == 1;
  loop assigns k, m;
*/
while (k+1<=l) {
      m = m+m;
      k = k+1;
  }

}
