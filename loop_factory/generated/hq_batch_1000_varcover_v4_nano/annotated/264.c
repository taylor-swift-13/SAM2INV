int main1(int a,int b,int k,int q){
  int l, i, v;

  l=34;
  i=0;
  v=i;

  
  /*@

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant v == 0;

    loop invariant l == 34;

    loop invariant a == \at(a, Pre);

    loop assigns i, v;

  */
  while (i<l) {
      v = v-v;
      i = i+1;
  }

}