int main1(int a,int n,int p,int q){
  int l, i, v;

  l=32;
  i=l;
  v=0;

  
  /*@

    loop invariant v == 0;

    loop invariant 0 <= i && i <= l;

    loop invariant l == 32;

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i >= 0;

    loop invariant i <= 32;

    loop invariant i <= l;

    loop invariant q == \at(q, Pre);

    loop invariant a == \at(a, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v-v;
      i = i-1;
  }

}