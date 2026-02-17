int main1(int a,int k,int n){
  int l, i, v, q;

  l=52;
  i=0;
  v=4;
  q=n;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (q == \at(n,Pre));

    loop invariant (i > 0) ==> (q % 2 == 0);

    loop assigns i, q;

    loop variant l - i;

  */
  while (i<l) {
      q = q+q;
      q = q+v;
      i = i+1;
  }

}