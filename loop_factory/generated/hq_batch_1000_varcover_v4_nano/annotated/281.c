int main1(int a,int b,int n,int p){
  int l, i, v, e, x, s;

  l=11;
  i=0;
  v=n;
  e=a;
  x=n;
  s=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 11;
    loop invariant 0 <= i <= l;
    loop invariant (i == 0) ==> (v == \at(n, Pre));
    loop invariant (i == 0) ==> (e == \at(a, Pre));
    loop invariant (i == 0) ==> (x == \at(n, Pre));
    loop invariant (i == 0) ==> (s == l);
    loop assigns v, e, x, s, i;
  */
while (i<l) {
      v = v*2;
      e = e/2;
      x = x*x+v;
      if (v+6<l) {
          e = e*x;
      }
      else {
          v = v*v+x;
      }
      if (v*v<=l+5) {
          e = e*e+v;
      }
      else {
          s = e*e;
      }
      i = i+1;
  }

}