int main1(int a,int b,int m){
  int l, i, v;

  l=(m%9)+13;
  i=0;
  v=-1;

  
  /*@

    loop invariant (0 <= i) && (i <= l);

    loop invariant l == (m % 9) + 13;

    loop invariant (v == -1) || (v == 0);

    loop assigns v, i;

    loop variant (l - i);

  */
  while (i<l) {
      v = v-v;
      if (v+2<l) {
          v = a-m;
      }
      v = v+i;
      v = v+1;
      v = v-v;
      i = i+1;
  }

}