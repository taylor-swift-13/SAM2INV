int main1(int a,int q){
  int n, v, j;

  n=q;
  v=0;
  j=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant v == 0 || v <= n;
  loop invariant (n >= 7) ==> j == 5 + v;
  loop invariant n == \at(q, Pre);
  loop invariant a == \at(a, Pre);

  loop invariant (n >= 0) ==> (v <= n) && (v >= 0) && (n == q);
  loop invariant (n >= 7) ==> (j == 5 + v) && (a == \at(a, Pre));
  loop invariant v >= 0 && j >= 5 && (n >= 0 ==> v <= n) && (n >= 0 ==> j <= 5 + n);
  loop invariant j >= 5;
  loop invariant n == q;
  loop invariant (n >= 7) ==> (j == 5 + v);
  loop assigns j, v;
*/
while (v+1<=n) {
      if (v+7<=v+n) {
          j = j+1;
      }
      v = v+1;
  }

}
