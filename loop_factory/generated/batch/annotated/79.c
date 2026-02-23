int main1(int a,int n){
  int i, l, k;

  i=n;
  l=0;
  k=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (l >= 0);

  loop invariant (i == \at(n, Pre));
  loop invariant ((k == 2) || (k == 0));
  loop invariant i == n;

  loop invariant l >= 0;
  loop invariant i == \at(n, Pre);
  loop invariant (i >= 0) ==> l <= i;
  loop invariant (l==0 ==> k==2) && (l>=1 ==> k==0);

  loop invariant (l == 0 ==> k == 2) && (l > 0 ==> k == 0);
  loop invariant a == \at(a, Pre);
  loop assigns k, l;
*/
while (l<i) {
      k = k-k;
      l = l+1;
  }

}
