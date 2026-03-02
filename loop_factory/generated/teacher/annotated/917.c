int main1(int b,int m){
  int a, j, v, n;

  a=b+25;
  j=a;
  v=0;
  n=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == b + 25;

  loop invariant (v < a/2) ==> (n == a);

  loop invariant (v <= a/2) ==> (n == a) && ((n - a) % 4 == 0);

  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n >= a;
  loop invariant (n - a) % 4 == 0;
  loop invariant 0 <= v;

  loop invariant v >= 0;
  loop invariant v <= a/2 ==> n == a;

  loop assigns n, v;
*/
while (v<a) {
      if (v>=a/2) {
          n = n+4;
      }
      v = v+1;
  }

}
