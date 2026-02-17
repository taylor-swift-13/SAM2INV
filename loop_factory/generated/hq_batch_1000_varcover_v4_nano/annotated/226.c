int main1(int b,int k,int q){
  int l, i, v;

  l=66;
  i=0;
  v=q;

  
  /*@

    loop invariant l == 66;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant (i == 0) ==> (v == q);


    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      v = v+v;
      v = v+i;
      i = i+1;
  }

}