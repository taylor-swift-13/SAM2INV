int main1(int b,int m,int q){
  int l, i, v;

  l=(m%6)+13;
  i=l;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0 && i <= l;
    loop invariant (i == l) ==> (v == l);
    loop invariant (i < l) ==> (v == 0);
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v+v;
      v = v+v;
      v = v+1;
      v = v+v;
      v = v-v;
      i = i-1;
  }

}