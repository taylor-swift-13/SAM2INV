int main1(int a,int p,int q){
  int l, i, v;

  l=32;
  i=0;
  v=a;

  
  /*@

    loop invariant i <= l;


    loop invariant (i > 0) ==> (v == -6);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = -5;
      v = v+1;
      v = v+1;
      v = v+v;
      i = i+1;
  }

}