int main1(int b,int m,int n,int p){
  int l, i, v;

  l=p+13;
  i=0;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant (i <= l) || (l < 0);
    loop invariant l == p + 13;
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant v >= 6;

    loop invariant (v + 8) % 14 == 0;
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant (v % 2) == 0;
    loop invariant (i == 0) ==> (v == 6);
    loop assigns i, v;
  */
while (i<l) {
      v = v+4;
      v = v+v;
      i = i+1;
  }

}