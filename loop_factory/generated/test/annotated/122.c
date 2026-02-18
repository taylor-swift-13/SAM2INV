int main1(int a,int n,int p,int q){
  int l, i, v;

  l=p;
  i=0;
  v=n;

  
  /*@


    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant (i > 0) ==> (v % 2 == 0);

    loop invariant 0 <= i;


    loop invariant l == p;

    loop invariant i >= 0;

    loop invariant l < 0 || (0 <= i && i <= l);

    loop invariant i == 0 ==> v == \at(n, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      v = v+v;
      i = i+1;
  }

}