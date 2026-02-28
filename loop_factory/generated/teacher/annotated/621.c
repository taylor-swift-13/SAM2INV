int main1(int k,int m){
  int n, d, s, r, b, g;

  n=m;
  d=0;
  s=k;
  r=k;
  b=n;
  g=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == k;
  loop invariant n == m;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m,Pre);

  loop invariant (k == 0) ==> (r == 0);
  loop assigns r;
*/
while (1) {
      r = r+s;
  }

}
