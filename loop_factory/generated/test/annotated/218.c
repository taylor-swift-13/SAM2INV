int main1(int a,int n){
  int l, i, v, q;

  l=n+19;
  i=0;
  v=l;
  q=i;

  
  /*@

    loop invariant l == n + 19;

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant 0 <= i;


    loop invariant l == \at(n, Pre) + 19;

    loop invariant i >= 0;

    loop invariant (i == 0) ==> (v == l);


    loop invariant i <= l || l < 0;


    loop invariant v >= l;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*2;
      i = i+1;
  }

}