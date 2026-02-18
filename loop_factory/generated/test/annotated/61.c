int main1(int a,int k,int n,int q){
  int l, i, v;

  l=(q%6)+9;
  i=0;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == (q % 6) + 9;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant (n == -1) ==> (v == -1);

    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;

    loop invariant 0 <= i && i <= l;

    loop invariant (i == 0) ==> (v == n);
    loop invariant i <= 14;
    loop invariant (i > 0) ==> (v % 2 != 0);
    loop assigns v, i;
    loop variant l - i;
  */
while (i<l) {
      v = v+v;
      v = v+1;
      i = i+1;
  }

}