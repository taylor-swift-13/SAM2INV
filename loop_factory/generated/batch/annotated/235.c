int main1(int m,int p){
  int n, v, c;

  n=49;
  v=0;
  c=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= n;
  loop invariant n == 49;
  loop invariant (\at(p, Pre) >= 42) ==> (c >= \at(p, Pre));
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= v;
  loop invariant v >= 0;
  loop assigns c, v;
*/
while (v<n) {
      if (c+7<n) {
          c = c-n;
      }
      else {
          c = c+c;
      }
      v = v+1;
  }

}
