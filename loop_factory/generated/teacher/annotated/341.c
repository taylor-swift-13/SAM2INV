int main1(int k,int m){
  int j, l, p;

  j=9;
  l=0;
  p=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= l <= j + 1;
  loop invariant l % 2 == 0;
  loop invariant (l == 0) ==> (p == m);
  loop invariant (l > 0) ==> (p >= 0);
  loop invariant j == 9;
  loop invariant 0 <= l;
  loop invariant l <= j + 1;
  loop invariant (l % 2) == 0;
  loop invariant l >= 0;

  loop assigns p, l;
*/
while (l<j) {
      p = p*p;
      l = l+2;
  }

}
