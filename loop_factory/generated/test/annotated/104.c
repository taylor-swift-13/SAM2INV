int main1(int a,int k,int m,int n){
  int l, i, v;

  l=42;
  i=l;
  v=m;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= 42;

    loop invariant l == 42;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant 0 <= i <= l;

    loop invariant (i == l) ==> (v == \at(m, Pre));

    loop invariant (i != l) ==> (v == 0);

    loop invariant a == \at(a,Pre) && k == \at(k,Pre) && m == \at(m,Pre) && n == \at(n,Pre);

    loop invariant i <= l;

    loop invariant (i == l) ==> (v == m);

    loop invariant (i < l) ==> (v == 0);

    loop assigns i, v;

    loop variant i;

  */
  while (i>0) {
      if (i+2<=n+l) {
          v = v+1;
      }
      if ((i%7)==0) {
          v = v-v;
      }
      else {
          v = v-v;
      }
      i = i-1;
  }

}