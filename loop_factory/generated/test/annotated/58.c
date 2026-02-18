int main1(int a,int k,int n,int p){
  int l, i, v;

  l=66;
  i=0;
  v=n;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 66;

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i;

    loop invariant (i == 0) || ((v + i + 1) % 2 == 0);

    loop invariant k == \at(k, Pre);


    loop invariant 0 <= i <= l;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+1;
  }

}