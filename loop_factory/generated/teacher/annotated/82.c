int main1(int m,int n){
  int x, l, j, v;

  x=n-9;
  l=0;
  j=n;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == \at(n, Pre) - 9;
  loop invariant j == \at(n, Pre);

  loop invariant (l == 0) ==> v == \at(m, Pre);

  loop invariant j == n;
  loop invariant x == n - 9;

  loop invariant (l == 0) ==> (v == m);
  loop invariant 0 <= l;
  loop invariant (x >= 0) ==> (l <= x);

  loop assigns v, l;
*/
while (l<x) {
      v = v+v;
      v = v+j;
      l = l+1;
  }

}
