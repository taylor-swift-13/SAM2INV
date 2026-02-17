int main1(int a,int b,int k){
  int l, i, v;

  l=41;
  i=l;
  v=-8;

  
  /*@

    loop invariant l == 41;

    loop invariant i >= 0;

    loop invariant i <= 41;

    loop invariant v == 0 || v == -8;

    loop invariant k == \at(k, Pre);

    loop assigns i, v;

    loop variant i;

  */
  while (i>0) {
      v = k-l;
      v = v+v;
      v = v-v;
      i = i-1;
  }

}