int main1(int b,int n){
  int a, o, v, k;

  a=b-7;
  o=0;
  v=b;
  k=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == b - 7;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant a == \at(b, Pre) - 7;
  loop invariant (7*k - 4*v == 8) || (7*k - 4*v == 3*b - 49);
  loop invariant 7*k - 4*v == 8 || (k == a && v == b);
  loop assigns k, v;
*/
while (1) {
      k = v;
      v = v+3;
      v = v+1;
      k = k+v;
      k = k+k;
      v = k-v;
      if (n<n+4) {
          v = v+k;
      }
  }

}
