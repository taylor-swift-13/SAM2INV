int main1(int a,int b,int q){
  int l, i, v;

  l=35;
  i=l;
  v=a;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant (i == l) ==> (v == a);

    loop invariant (i < l) ==> (v == 0);

    loop assigns i, v;

    loop variant i;

  */
  while (i>0) {
      v = v-v;
      v = v+v;
      v = v+v;
      i = i/2;
  }

}