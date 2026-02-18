int main1(int a,int n,int p,int q){
  int l, i, v;

  l=36;
  i=0;
  v=a;

  
  /*@

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant l == 36;

    loop invariant a == \at(a, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant n == \at(n, Pre);

    loop invariant i >= 0;

    loop invariant q == \at(q, Pre);

    loop invariant 0 <= i && i <= l;


    loop invariant (i > 0 && !(p < a + 5)) ==> (v % 2 == 0);

    loop invariant (i == 0) ==> (v == a);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
        v = v+v;
        if (p<a+5) {
            v = v+1;
        }
        i = i+1;
  }

}