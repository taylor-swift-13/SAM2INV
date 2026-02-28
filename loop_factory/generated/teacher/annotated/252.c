int main1(int b,int p){
  int u, v, e, n;

  u=p-7;
  v=0;
  e=u;
  n=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == \at(p, Pre) - 7;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant n >= 0;
  loop invariant u == p - 7;
  loop invariant e <= u;

  loop invariant (e > n) ==> (e - n) >= 0;
  loop invariant (e <= n) ==> (n - e) >= 0;
  loop assigns e, n;
*/
while (e!=0&&n!=0) {
      if (e>n) {
          e = e-n;
      }
      else {
          n = n-e;
      }
  }

}
