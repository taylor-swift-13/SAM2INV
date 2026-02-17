int main1(int a,int b,int k,int q){
  int l, i, v;

  l=34;
  i=0;
  v=i;

  
  /*@

    loop invariant l == 34;

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == 0);

    loop invariant i >= 0;

    loop invariant v >= 0;

    loop assigns i, v;

  */
  while (i<l) {
      v = v-v;
      v = v-v;
      v = v+1;
      v = v+1;
      v = v+1;
      v = v+v;
      i = i+1;
  }

}