int main1(int n,int q){
  int l, i, v;

  l=21;
  i=0;
  v=q;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant l == 21;

    loop invariant q == \at(q, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant 0 <= i && i <= l;

    loop invariant 0 <= i;

    loop invariant (i == 0) ==> (v == q);

    loop invariant (i > 0) ==> ((i >= 1 && i <= 9) ==> v == q * 2);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if ((i%9)==0) {
          v = v+v;
      }
      i = i+1;
  }

}