int main1(int b,int k){
  int l, t, n;

  l=48;
  t=0;
  n=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t <= l && (t == 0) ==> (n == b) && (t > 0) ==> (n == 0) && l == 48;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant l == 48;
  loop invariant 0 <= t;
  loop invariant t <= l;
  loop invariant (t == 0) ==> (n == \at(b, Pre));
  loop invariant (t > 0) ==> (n == 0);
  loop invariant (t == 0) ==> (n == b);
  loop invariant (t==0 ==> n == \at(b, Pre)) && (t>0 ==> n == 0);
  loop assigns n, t;
*/
while (t<l) {
      n = n-n;
      if (t+6<=k+l) {
          n = n+n;
      }
      t = t+1;
  }

}
