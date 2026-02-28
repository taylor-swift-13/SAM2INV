int main1(int p){
  int q, n, v, l;

  q=p+5;
  n=0;
  v=q;
  l=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == p + 5;
  loop invariant n == 0;
  loop invariant 0 <= n;


  loop invariant p == \at(p, Pre);
  loop invariant (n < q/2) ==> v - l == 5;

  loop invariant q == \at(p, Pre) + 5;



  loop assigns v, l;
*/
while (n<=q-1) {
      if (n<q/2) {
          v = v+l;
      }
      else {
          v = v+1;
      }
      l = l+l;
  }

}
