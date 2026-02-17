int main1(int k,int m,int n){
  int l, i, v;

  l=61;
  i=0;
  v=k;

  
  /*@

    loop invariant l == 61;

    loop invariant 0 <= i && i <= l;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant i > 0 ==> v == 0;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v-v;
      if (k<i+1) {
          v = v+v;
      }
      v = v+v;
      v = v+1;
      if (v+3<l) {
          v = v-v;
      }
      i = i+1;
  }

}