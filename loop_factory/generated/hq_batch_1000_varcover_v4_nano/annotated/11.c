int main1(int b,int k,int m){
  int l, i, v;

  l=49;
  i=l;
  v=b;

  
  /*@

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == 0 || v == b;

    loop assigns i, v;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      v = v-v;
      i = i/2;
  }

}