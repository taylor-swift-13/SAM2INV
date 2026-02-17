int main1(int a,int m,int n){
  int l, i, v;

  l=16;
  i=l;
  v=l;

  
  /*@

    loop invariant (v == 1) || (i == l && v == l);

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant l == 16;

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v+v;
      v = v-v;
      v = v-v;
      v = v-v;
      v = v+1;
      i = i-1;
  }

}