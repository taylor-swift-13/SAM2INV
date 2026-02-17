int main1(int k,int n,int p){
  int l, i, v;

  l=75;
  i=0;
  v=n;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant l == 75;

    loop invariant k == \at(k,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant (i == 0) ==> (v == \at(n,Pre));

    loop invariant (i > 0) ==> (v == -3);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      v = v+v;
      v = -8;
      v = v+5;
      i = i+1;
  }

}