int main1(int a,int n,int p,int q){
  int l, i, v;

  l=40;
  i=0;
  v=q;

  
  /*@

    loop invariant l == 40;

    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (v == \at(q, Pre));


    loop invariant q == \at(q,Pre);

    loop invariant a == \at(a,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant p == \at(p,Pre);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant (i > 0) ==> (v >= 0);

    loop invariant (i == 0) ==> (v == q);


    loop invariant q == \at(q, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      if (v+5<l) {
          v = v+i;
      }
      else {
          v = v-v;
      }
      if (v+5<l) {
          v = v-v;
      }
      i = i+1;
  }

}