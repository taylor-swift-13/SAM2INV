int main1(int k,int m,int n,int q){
  int l, i, v;

  l=34;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i % 3 == 0;
    loop invariant i <= l + 2;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);

    loop invariant v % 2 == 0;
    loop invariant v >= 34;
    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop invariant l == 34;
    loop invariant (i % 3 == 0);
    loop invariant (i >= 0);
    loop invariant (v >= 34);
    loop invariant (k == \at(k, Pre));
    loop invariant (m == \at(m, Pre));
    loop invariant (n == \at(n, Pre));
    loop assigns i, v;
    loop variant l - i;
  */
while (i<l) {
      v = v+5;
      v = v+6;
      if ((i%3)==0) {
          v = v+v;
      }
      i = i+3;
  }

}