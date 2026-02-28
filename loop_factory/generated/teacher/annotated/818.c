int main1(int b,int k){
  int n, q, v, u;

  n=(k%11)+20;
  q=3;
  v=0;
  u=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant n == (k % 11) + 20;
  loop invariant 0 <= v <= n;
  loop invariant (v <= n/2) ==> (u == 3*v);
  loop invariant 0 <= v;
  loop invariant v <= n;
  loop invariant (b == \at(b, Pre));
  loop invariant (k == \at(k, Pre));
  loop assigns u, v;
*/
while (v<n) {
      if (v<n/2) {
          u = u+3;
      }
      else {
          u = u-3;
      }
      v = v+1;
  }

}
