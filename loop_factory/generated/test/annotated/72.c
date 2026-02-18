int main1(int a,int k,int n,int q){
  int l, i, v;

  l=k;
  i=0;
  v=-2;

  
  /*@

    loop invariant l == \at(k, Pre);

    loop invariant i >= 0;


    loop invariant (i > 0) ==> (v == 0);

    loop invariant a == \at(a, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant l == k;

    loop invariant k == \at(k, Pre);

    loop invariant (i <= l) || (l <= 0);

    loop assigns v, i;

  */
  while (i<l) {
      v = v+i;
      v = v-v;
      i = i+1;
  }

}