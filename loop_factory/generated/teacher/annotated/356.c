int main1(int b,int k){
  int e, n, v, f;

  e=44;
  n=0;
  v=b;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant e == 44;
  loop invariant n == 0;
  loop invariant v >= \at(b, Pre);
  loop invariant (b >= 0) ==> (f <= v);
  loop invariant n <= e;
  loop invariant (v - b) % 5 == 0;


  loop invariant v >= b;

  loop invariant (n > 0) ==> (f == v - 2);
  loop invariant 0 <= n;
  loop assigns f, v;
*/
while (n<e) {
      f = v;
      v = v+2;
      v = v+3;
      f = f+3;
  }

}
